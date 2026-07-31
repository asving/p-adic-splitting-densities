# ROOT ASSEMBLY — the uniformity theorem, composed from the leaves (unit ROOT, 2026-08-02)

**Phase C spine.** This is the document the end-to-end verifiers read: the uniformity
theorem stated in Asvin's scaffold form, its proof as a LINEAR COMPOSITION of the
Phase-B leaves, and the COMPLETE conditionality ledger. It is built at the wave-10
state of the campaign (ledger `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"WAVE 10
+ PASS-2 ADJUDICATIONS", HEAD d730669) from `docs/MATH_COMPLETION_TREE_2026-08-01.md`
(+ DELTAs 1–3, whose corrected readings govern), the per-leaf attempt/verify records in
`lean/notes/openmath/`, and the literature unit `lean/notes/openmath/LITUNIT_2026-08-01.md`.

**Honesty headline (read first).** The theorem below is NOT yet a verified complete
proof, and this document does not claim it is. **REVISION 1 applied** (appendix §7,
2026-08-02): the Phase C end-to-end pass 1 (VC1, Codex, fresh context;
`lean/notes/openmath/VC1_root.jsonl`) returned **COMPOSITION-GAPS** (blockers 1–8,
advisories 9–11); every finding is dispositioned in §7 and repaired in place below, and
statuses are synced to the 2026-08-02 harvest (ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` final sections, commit c43b13b).
**REVISION 2 applied** (appendix §8): the end-to-end pass 2 (VC2, Codex, fresh
context; `lean/notes/openmath/VC2_root.jsonl`) returned **COMPOSITION-GAPS** (5
blockers V2-1/2/4/5/6, 2 advisories V2-3/7); every finding is dispositioned in §8 and
repaired in place below — headline repairs: the clause-(R) self-loop formula is now
quantified e ≥ 2 with the forcing proof DISPLAYED (the (SL≥2) display at Step 5), and
(H4) is SPLIT into (H4a) = (R1)–(R4) (consumed by clause (R) too, not (UB)-only) +
(H4b) = (UB-X). **REVISION 3 applied** (appendix §9): the end-to-end pass 3 (VC3,
Fable, fresh context — the model-diverse pass;
`lean/notes/openmath/VC3_root_fable_verify.md`) returned **COMPOSITION-GAPS** (4
blockers B1–B4, 4 advisories A5–A8 — ALL attribution/ledger-integrity; VC3 explicitly
CONFIRMED the composition's mathematics: acyclicity edge-by-edge incl. 17 ≺ 18 ≺ 18b,
the (ROOT-C)-hypotheses ↔ §3.1-[M]-rows bijection, the (SL≥2) display, the (S3)
split); every finding is dispositioned in §9 and repaired in place below, and
statuses are synced to the 2026-08-02-night harvest (ledger 7b28562: **VERIFIED = 6**).
**REVISION 4 applied** (appendix §10): the end-to-end pass 4 (VC4, Codex, fresh
context; `lean/notes/openmath/VC4_root.jsonl`) returned **COMPOSITION-GAPS** (4
blockers + 1 advisory, findings VC4-1..VC4-5 — again all attribution/ledger
integrity; VC4's own pass-list re-confirmed acyclicity incl. 17 ≺ 18 ≺ 18b, (SL≥2),
and the repaired Step-19 Σ_τ R_τ = 1 derivation); every finding is dispositioned in
§10 and repaired in place below — headline repairs: a NEW §3.1 [M] row **(PACK)**
(D-11's open clause 4, the actual-pack correspondence) carried as hypothesis
**(H5)**; clause (SQ)'s attribution corrected DOWNWARD (unconditional — a favorable
honesty fix); the (ADM) row rewritten to its single operative FULL-attainment form
(O-9 r4); and statuses synced to the confirming-passes harvest (**VERIFIED = 7**).
What exists is: an acyclic composition (acyclicity now holds edge-by-edge: the Step-1 edge
REMOVED by re-pointing to Dfloor's self-contained Appendix A, the D-11/O-11 cycle
STRATIFIED as Step 17 ≺ Step 18 ≺ Step 18b) in which every step is a named leaf with an
on-file proof, SEVEN of the leaves VERIFIED through the campaign's two-pass
model-diverse bar (O-13, O-12, Dfloor, GD23, CU-1, O-10, O4T — the last adjudicated
at the confirming-passes harvest after its clean acceptance pass, REVISION 4 status
sync), the rest PROVED-UNVERIFIED with
their pending passes NAMED, and the genuinely open mathematics confined to §3.1: the
two heavy items — **(GR-B)** at OM orders ≥ 2 and **(FRESH)** — both pinned to printed
literature statements and priced at a single lemma layer, plus the smaller displayed
rows ((R1)–(R4) with the clause-(UB) residue (UB-X), D-12r, (E-N), — added at
REVISION 2 — (ADM), O-9's census-admissibility hypothesis (FULL attainment since O-9
r4; automatic at order 0 only), and — added at REVISION 4, finding VC4-3 — **(PACK)**,
the actual-pack correspondence). **THE THEOREM AS
PRESENTLY PROVED is the conditional form (ROOT-C) displayed in §1**; the unconditional
(ROOT) is the TARGET, quantifier-for-quantifier NOT yet what the steps prove. §3 is the
complete list of everything the root currently rests on beyond literature; §4 is the
literature roster (the goal's conditionality class); §5 is the numerics corroboration
index (flags, never substitutes). The tree's §4 acceptance criterion applies verbatim:
PROVED-UNVERIFIED is never consumed by an acceptance claim, and this assembly becomes
THE COMPLETE PROOF only when §3's ledger empties into VERIFIED + LITERATURE-audited.

**Status vocabulary** (tree §0, compressed): **VERIFIED** = survived ≥ 2 consecutive
clean adversarial passes in fresh contexts, at least two models (VERIFIED-DUAL), or
machine-checked in Lean with a faithfulness audit (VERIFIED-LEAN). **PROVED-UNVERIFIED**
= proof on file, pending pass named. **OPEN** = no proof. **LITERATURE** = external
citation carries it, faithfulness status stated. A reduction is not a proof.

---

## 1. THE THEOREM (the scaffold form)

Fix n ≥ 2. A **splitting type** τ of degree n is a multiset of pairs (e_i, f_i) with
Σ e_i f_i = n — the ramification indices and residue degrees of the irreducible
ℚ_p-factors. (The tree writes σ for the same object; τ = σ throughout.) Monic degree-n
polynomials over ℤ_p are identified with ℤ_p^n by coefficients, carrying Haar
probability μ. decided_τ(k) counts the residue classes mod p^k ALL of whose monic lifts
are separable of type τ; undec(k) is the measure of the classes not decided for any
type. Let ℛ := ℚ[q, 1/q, 1/(q^c − 1) : c ≥ 1] ⊂ ℚ(q) — the cyclotomic-type ring, whose
elements have no poles at any real q ≥ 2, hence at any prime power.

> **(ROOT) THE UNIFORMITY THEOREM — THE TARGET.** (Displayed as the campaign's goal;
> NOT what the §2 steps presently prove — that is (ROOT-C) below, the honest
> quantifier-for-quantifier form.) For each n and each splitting type τ of degree n
> there is a SINGLE rational function R_τ ∈ ℛ ⊂ ℚ(t) such that at EVERY prime p —
> including every wild prime p ≤ n — the following hold.
>
> **(0) Cylinder-limit density.** The type-τ locus L_τ = {f monic separable of type τ}
> is Borel; the decided-τ cylinder unions are nested increasing in k; and
>
>     α(n, τ; p) := μ(L_τ) = lim_{k→∞} decided_τ(k) / p^{nk}.
>
> **(SQ) Level-k squeeze.** At every finite level k, two-sidedly,
>
>     decided_τ(k)/p^{nk}  ≤  α(n, τ; p)  ≤  decided_τ(k)/p^{nk} + undec(k),
>
> and undec(k) → 0 (drainage) — so the finite-level counts converge to the density
> with an explicit bracket at every k.
>
> **(R) R_τ evaluation.** R_τ is the τ-entry of the unique solution of a finite linear
> system (I − K(q))·C = b(q) over ℚ(q) — branch = convolution over coprime children,
> descend = strictly smaller child, self-loop of size e (**e ≥ 2 always** — no size-1
> self-loop exists in the system; the forcing is the (SL≥2) display at Step 5
> [REVISION 2, finding V2-6]) = geometric resummation 1/(1 − q^{−(e(e+1)/2 − 1)})
> (a unit of ℛ, the exponent being e(e+1)/2 − 1 ≥ 2) — a system whose state
> menu, coefficients, and pivots carry NO
> dependence on p; every denominator produced anywhere in the solve is cyclotomic-type
> (a unit of ℛ), so the specialization is pole-free at every prime power; and
>
>     α(n, τ; p) = R_τ(p),      Σ_τ R_τ = 1  identically in ℚ(t).
>
> **(UB) Unramified base.** The SAME R_τ works over every unramified base: over the
> degree-δ unramified extension of ℚ_p the type-τ density is R_τ(p^δ).

> **(ROOT-C) THE COMPOSED THEOREM (what §2 proves, stated exactly).** Assume the §3.1
> open-mathematics rows as hypotheses:
> **(H1)** (GR-B) at OM orders ≥ 2; **(H2)** (FRESH); **(H3)** D-12r (the TB-CAP
> (τ-irr) perimeter), (E-N), and (ADM) (O-9's census-admissibility hypothesis,
> FULL attainment — automatic at order 0 only; at r ≥ 1 a displayed p-free
> per-datum decidable check — §3.1) [(ADM) added at REVISION 2, finding V2-5; its
> "automatic at orders ≤ 1" phrasing corrected at REVISION 4, finding VC4-2, per
> the O-9 r3/r4 rescopes];
> **(H4a)** (R1)–(R4) [SPLIT out of the former (H4) at REVISION 2, finding V2-2:
> NOT clause-(UB)-only — clause (R)'s value chain consumes it too, through Step 18's
> K3-c (the base-changed β-legs at q ↦ q^δ, δ > 1; the O-11 r2 declared row D-c)];
> **(H4b)** the clause-(UB) residue (UB-X) (the per-leaf O_δ
> re-base audit + position-class exhaustion + aggregation commutation — §3.1),
> whose position-class-stability fragment **(K3-δ)** (K3-c's realized δ > 1 pools
> are δ-stable position classes — (UB-X)(b) restricted to those pools) is ALSO
> consumed by clause (R) [REVISION 4, finding VC4-1];
> **(H5)** (PACK), the actual-pack correspondence (D-11's open clause 4: the
> concrete assembled pack's rows equal the intended 𝔅_n instantiation's
> entry-for-entry — §3.1) [added at REVISION 4, finding VC4-3].
> Then for each n ≥ 2 and each splitting type τ of degree n there is a single
> R_τ ∈ ℛ such that clauses (0), (SQ), (R) hold at EVERY prime p including every wild
> p ≤ n, and clause (UB) holds. Hypothesis attribution, exact [REVISION 2, finding
> V2-2; corrected at REVISION 4, findings VC4-1/VC4-3/VC4-4]: clause (0) rests on
> Step 1 alone (unconditional); clause (SQ) — under this section's SEMANTIC
> definitions of decided_τ(k) and undec(k) — rests on Step 1's bracket (Corollaries
> BRACKET/SEM-DRAIN) + Step 13's semantic drainage layer, both unconditional at
> every prime including wild: **it consumes NO §3.1 row** [attribution corrected
> DOWNWARD at REVISION 4, finding VC4-4 — the former display over-attributed
> (H1)–(H3), including (ADM) and the conditional classifier-transfer route, to
> (SQ); the classifier-side counting machinery rides the evaluation squeeze inside
> clause (R)'s scope instead]; clause (R) consumes (H1)–(H3) + (H4a) + (H5) + the
> (K3-δ) fragment of (H4b);
> NO clause other than (UB) consumes (H4b) BEYOND its (K3-δ) fragment; clause (UB)
> consumes
> **(H1)–(H3) + (H4a) + (H4b) + (H5)** [attribution COMPLETED at REVISION 3, finding B1: the
> former display read "(H4a) + (H4b)" as (UB)'s full set — but (H1) enters (UB)
> through Steps 8/16 (the GD layer, (GR-B)-conditional at orders ≥ 2), (H2)/(H3)
> through Step 16's consumption of Step 14's census ((FRESH)/(ADM)-conditional at
> orders ≥ 2) and through the (UB-X)(a)-transported dictionary/CU/drainage layers
> (D-12r, (E-N)); only (H4b) is (UB)-exclusive].
> Without (H4b), what is proved of (UB) is exactly the Step-16 scope: the GD/census
> layers hold over an arbitrary absolutely-unramified complete DVR (consuming neither
> (H4a) nor (H4b), while retaining their own (H1)–(H3) conditionality at orders ≥ 2 —
> finding B1), and — still under (H4a) — the alphabet law (F_{p^δ}-linearity +
> a_δ = δ·a₁) at δ-stable position classes. (The former "Without (H4)" sentence
> asserted the alphabet law hypothesis-free — false as written, since the law is
> (R1)–(R4)-conditional; corrected here.)
> **Proof status of the implication itself:** it is the §2 composition — seven leaves
> VERIFIED, the rest PROVED-UNVERIFIED with named pending passes (§3.2) and displayed
> transcription debts (§3.3). The [V]/[T] rows are AUDIT debts on the proof of this
> implication, not additional mathematical hypotheses of its statement; the
> implication is therefore itself PROVED-UNVERIFIED (never consumed by an acceptance
> claim) until §3.2/§3.3 empty and the end-to-end passes land. (ROOT) = (ROOT-C) +
> discharge of (H1), (H2), (H3), (H4a), (H4b), (H5).

**Wild-prime scope, explicit.** The content is at p ≤ n (p | n!), where factorization
is governed by higher-order Okutsu–Montes (OM) Newton-polygon towers whose combinatorics
a priori depend on p; p > n is residue-field combinatorics. The paper's original tame
route (S_n-equivariant resolution) FAILS at p ≤ n and is used nowhere below: every step
computes the wild densities directly.

**Relation to the tree's root.** (0)+(SQ) = (U-GEN)(i)/(ii) + the D-1 bridge; (R) =
(U-GEN)(iii) + D-6 + D-2; the operative claim is (U-GEN), and (U-GEN) ⇒ (U-DENS) via
(0) (the converse is not claimed — DELTA-1 §D1.5(a)). "Every prime" (as opposed to
"every prime outside an explicit finite effectively-bounded set") is carried by K-13 +
O-12. The projective normalization and the palindromic functional equation are ANNEX
(A-1/A-2, out of the critical path by standing directive).

**Verified instances (anchors, not proofs of the general theorem):** n = 2 is
VERIFIED-LEAN at every prime including wild p = 2 (`OM/UniformCapstone.montes_uniform_n2`,
Lean-core footprint: value + bracket + drainage machine-checked); n = 3 numerically
exact at the gate standard (RESUM-n3, 65/65, PARI 0 mismatches); the density tie
numerically confirmed through n ≤ 5 including deep-wild (5,5) (N2). O-11's falsifier
re-derived the true n = 2 triple (p/(2(p+1)), p/(2(p+1)), 1/(p+1)) from the REAL
assembled pack identically in ℚ(q).

---

## 2. THE PROOF (a linear composition of the leaves)

Each step names: the leaf/node (tree id) · its exact statement (compressed, faithful) ·
its verification status with the pass records · what it consumes. The steps are in
logical order; no step consumes a later one (the O-2/O-3 cycle was decomposed at
DELTA-2 §D2.3 — the K-RUN-C composition replaced the joint induction; the D-11/O-11
cycle VC1 found in the original walk is stratified at REVISION 1 as Steps 17/18/18b,
and the Step-1 forward edge is re-pointed — see §7). Standing
preconditions throughout (tree §2.4): f monic separable; trees range over ns-free
carriers; statements are per-f (selected-f) except where D-15 owns box quantification.

### Movement I — the measure floor and the symbolic engine

**Step 1 (D-1 MEAS-BRIDGE + D-2 SUM-ONE + D-4 BASE-CASES — the assembly floor;
"Dfloor").** Statement: (D-1) L_τ is Borel; level-k classes are cylinders of mass
p^{−nk}; decided unions nest; ∪_k decided_τ(k) = L_τ up to Haar-null; continuity from
below gives clause (0) — proved for both decided conventions in circulation, clause
(iv) EXACT in the strict convention; plus Corollaries BRACKET / SEM-DRAIN /
SEM-DRAIN-RATE = the measure content of (SQ) on the SEMANTIC side, unconditional at
every prime including wild. (D-2) every monic separable f has exactly one type
(unique factorization + defectlessness); the nonseparable locus is Haar-null — proved
SELF-CONTAINED inside this leaf (Dfloor Appendix A, via LIT-8c resultant/Vandermonde;
part of the VERIFIED leaf-#3 perimeter). [REVISION 1, finding 1: the original text
attributed ns-null to T-6's (ns-null) clause, a Step-2 node — a silent forward edge.
The dependency is RE-POINTED to Appendix A, which is what the verified leaf actually
proves; T-6's (ns-null) is the SAME fact proved independently at the T-layer (Step 2)
and is NOT consumed here. The edge is removed, not waived.] Hence **Σ_τ α(n,τ;p) = 1
at every p**, plus the interpolation principle (a rational function agreeing with a
constant at infinitely many arguments equals it). [REVISION 3, finding B3: the former
text concluded "Σ_τ R_τ = 1 in ℚ(t)" INSIDE this statement — beyond the leaf's
declared perimeter (R_τ is not even definable at Step 1, and α = R_τ needs Steps
18/18b), a textual forward edge contradicting this step's own Consumes-line. Dfloor's
VERIFIED statement supplies exactly Σ_τ α = 1 + the principle; the identity
Σ_τ R_τ = 1 is CONCLUDED at Step 19, inside clause (R)'s conditional scope.] (D-4)
the degree-1/0 floor: type {(1,1)} density 1 decided at
k = 0; empty-convolution unit conventions (C0)–(C2).
Status: **VERIFIED — leaf #3** (pass 1 Codex V22 CLEAN SOUND, 0 criticals, commit
604621f; pass 2 fresh Fable, model-diverse, 0 criticals, commit bdc996a; adjudicated at
ledger dbccbc1; falsifier `verification/openmath/dfloor_checks.py` ALL PASS). Three
minor gaps ride the next doc touch. Displayed residue: the **BASE-1(f) fence** — the
classifier-side (algorithmic) half at n = 1 is fenced OUT to the classifier steps below.
Consumes: LIT-2 (defectlessness; the K-11/M16 audited e·f bridge), LIT-8c
(resultant/Vandermonde — carries Appendix A's ns-null), standard measure theory with
displayed statements (Folland-grade; §4 roster). NOTHING from any later step.
Delivers to the root: clause (0), the bracket shell of (SQ), and the Σ_τ α = 1
identity + interpolation principle feeding (R)'s Σ_τ R_τ = 1 (concluded at Step 19 —
REVISION 3, finding B3).

**Step 2 (T-1..T-9 + T-U — the MOVES core: the symbolic engine).** Statement: the
carry-algebra stage tower and move ledger (T-1), composition of per-move digit/threshold
ledgers along read histories (T-2), the per-shape-prefix mass laws SUM/EVENT on the
branch tree T_can(f) (T-3), the finite p-free species/letter catalogue (T-4), the
height-resummation domains (T-5), tree assembly + (ns-null) + TB-CAP (T-6), the
per-species symbolic value tables + obligations ledger (T-7s, the symbolic half of the
T-7 split), the finite block-triangular solve with spectral escape over ℚ(q) (T-8), the
exhaustion index table (T-9), and THEOREM U — the squeeze closer, conditional on its
displayed kernel ledger §U.SQ.6 (T-U).
Status: **VERIFIED-DUAL, every node** (passes named per node in the tree §2.2;
2026-07-26/28), WITH the DELTA-1 re-scopings governing: T-1 is verified AS A THEOREM
ABOUT THE SYMBOLIC ENGINE (the semantic "each OM read" clause routes through the
dictionary steps below — §D1.5(e)); T-8 is verified for the formal ℚ(q) solve +
(REG-p)-conditional specialization (§D1.5(f)); T-7's value-correctness event
([1v]-FULL) is RE-OWNED by O-11 (D-9); T-6's TB-CAP is perimeter-conditional on D-12r.
Twenty-two sealed numeric gates ride this layer (§5).
Consumes: B-1..B-7, the June skeleton, with grades DISPLAYED HERE so the dependency
universe is closed inside this document [REVISION 1, finding 3]: **B-1** (Hensel
residue-splitting measure-exact) PROVED-UNVERIFIED (June document; 2000/2000
unit-resultant checks) — and the MOVES layer re-proves the split it needs inside
T-1..T-3; **B-2** (residue shape counts are universal polynomials) PROVED-UNVERIFIED at
document level with the counting core VERIFIED-LEAN (`L3.lean`/`L3Gauss.lean`/
`L3Squarefree.lean`, Lean-core); **B-3** (Newton-cell volume) core VERIFIED-LEAN
(`L4.lean` `cellVolume_eq`) + PROVED-UNVERIFIED document; **B-4** (order-r residual
equidistribution) order 1 = B-3 (VERIFIED-LEAN), order r PROVED-UNVERIFIED
(`M6_lemma.md`; its modern descendant is O-9's OL-B, discharged to GD-3); **B-5**
(Vandermonde pushforward) PROVED-UNVERIFIED (`R1_complete.md`); **B-6** (termination +
finite shape menu) PROVED-UNVERIFIED (`L5fix_complete.md`; modern face = O-13, Step 3);
**B-7** (finite linear solve) PROVED-UNVERIFIED (`L6M4_complete.md`; modern VERIFIED
counterpart = T-8 + K-13). The B-layer verification rounds are a §3.2 ledger row. B-8
is SUPERSEDED by this layer and cited nowhere.
Delivers: the entire p-free symbolic pipeline behind clause (R) — menu, tables, solve,
squeeze shell.

**Step 3 (O-13 + D-12 — skeleton/menu finiteness).** Statement: run-collapse is
well-defined; every realized T_can(f) (infinite branches included) collapses to a
finite tree (≤ 6n² letter blocks per branch); the collapsed shapes form the finite
p-FREE set Sk(n), |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)}. This survives the K-3 caterpillar
countermodel because unbounded recentering runs collapse to one node with a depth
parameter, never new shapes.
Status: **VERIFIED at honest scope — leaf #1** (pass 1 Codex V8 SOUND-WITH-GAPS → rev 2;
pass 2 fresh Fable, model-diverse, package-only context: all six gaps non-consumed
cosmetics, enumerator re-implemented from the text alone reproducing
|S_n| = 1, 15, 53, 197, 509, 1460 exactly; ledger "O-13 REACHES VERIFIED, 2026-07-31
night"). Lean: `skeleton_finite n` at every n (`SkeletonFinite.lean`). Displayed
residue: **D-12r** — the completeness clause (realized trees spell inside Sk(n)) rides
TB-CAP's D4R.0-K(c) verdict pin, a SEPARATE node. VAL-DIV is a labeled conjecture,
consumed by nothing here.
Consumes: T-4's letter finiteness (VERIFIED-DUAL), the B-6 depth mechanism
(PROVED-UNVERIFIED, grade displayed at Step 2's consumption list; §3.2 B-layer row).
Delivers: finiteness of the solve's state menu in clause (R), and K-OB-A's roster
finiteness (CU-5).

### Movement II — the solve's regularity (pole-freeness at every prime power)

**Step 4 (K-13 — (REG-p) finiteness; Lean-formalized).** Statement: the set of primes
where the pinned rational data degenerate is finite, exactly characterized, effectively
bounded; Theorem U fires at a cofinite set. Status: **PROVED + VERIFIED-LEAN** (M17
Theorems A/B/C + Corollary U; `MovesU/RegPFinite.lean`, 14 theorems, Lean-core; N6
25/25). Consumes: T-8's formal solve. Delivers: (R) at all but finitely many primes —
upgraded to ALL primes by Step 5.

**Step 5 (O-12 + D-6 — pole-free / (REG-p)-emptiness at the intended solve family
𝔅_n).** Statement: at the abstract solve family 𝔅_n (the §2.1-defined intended
instance), for all three on-record kernel organizations, EVERY block determinant and
EVERY assembled denominator — table coefficients, height resummations, normalizations,
the final R_τ — is cyclotomic-type (a unit of ℛ), hence nonvanishing at every prime
power ≥ 2: the failing set is EMPTY (Theorems 1 + 3 + 4 + Lemma RR; substochasticity +
termination margins ≥ 3/4, 7/8, 6/7 ⇒ spectral radius < 1). Includes the semantic mass
lemma base L1–L6′/Fact F that Step 17 consumes.
Status: **VERIFIED at honest scope — leaf #2** (pass 1 Codex V19 no criticals; pass 2
fresh Fable ZERO criticals, 2 non-load-bearing gaps; adjudicated at ledger commit
95a46d2; falsifier 18,120 prime powers 0 findings, extended by D-11's run to 303/303
primes < 2000). The honest scope: zeros/poles at 𝔅_n — VALUE correctness is NOT part of
this claim (that is D-11 + O-11); the extension to the eventual general-n pack is gated
by D-11 (instance pin) + the contingent OL-O12-1 (fires only if a future pack departs
from 𝔅_n's organizations). Residue: **OL-O12-2** — mathematical half CLOSED at the D-11
unit; what remains is a finite transcription/data pass, zero mathematics.
**(B-INST) — the instance correspondence, stated exactly [REVISION 1, finding 9].**
What identifies the realized packs with 𝔅_n, per n: the pack consumed by Steps 17/18
is BY CONSTRUCTION the 𝔅_n member assembled from T-4's menu, T-7s's tables, and T-8's
block organization (tree §2.1's definition of the intended instance) — the O-12
theorems apply to it verbatim PROVIDED its kernel organization is one of the three
on-record, and OL-O12-1 (contingent, currently unfired) is the displayed escape if a
future pack departs. NO supplied theorem identifies "every general-n realized pack"
with 𝔅_n beyond this by-construction pin: at n = 3 the identification of the complete
realized degree-3 table as an (O3) member of 𝔅₃ is the OL-O12-2 data pass (§3.3, owed);
at general n it is D-11's instance pin (Step 17) + the same finite transcription
discipline, which is exactly why D-11 sits on the mandatory path.
**(SL≥2) — every self-loop has size e ≥ 2; the e = 1 corner is VACUOUS [REVISION 2,
finding V2-6].** The §1 clause-(R) denominator 1/(1 − q^{−(e(e+1)/2 − 1)}) degenerates
at e = 1 (exponent 0, denominator 0); it never fires there, by the solve structure —
proof displayed, each step a proved O-12 clause (`O12_phaseB_verifybrief_rev4.md`
§§2.2–2.4, Thm 1, Cor D):
(a) *self-loops live inside one block.* Every INTER-block booking descends strictly —
hand-off targets have multiplicity m < e resp. μ < e (Lemma L4(i)/(ii)) — so the block
solve is triangular with the within-block (S-loop) return as the ONLY diagonal entry:
a self-loop of the system IS a block-e loop, and no cycle through distinct blocks
exists.
(b) *block 1 has no loop.* K_1 = (0), Φ_1 = 1, E(1) = {1} (O-12 §§2.2–2.3; Theorem 1
is stated "for e ∈ {2, …, n} (block 1 has K_1 = 0, Φ_1 = 1)"): a size-1 aligned
cluster is a monic linear factor, decided immediately (β_1 = 1 — also the base case
of D-11 M2's induction); and multiplicity-1 hand-off atoms TERMINATE as simple Hensel
factors, absorbed into the composition datum as fixed data — they never open a
continuation state, so nothing ever re-enters block 1.
(c) *hence e ≥ 2 at every self-loop*, so E = e(e+1)/2 ≥ 3, the exponents E − 1 ≥ 2 and
E ≥ 3 are ≥ 1, and every solve denominator u ∈ {1 − q^{1−E}, 1 − q^{−E}} is a unit of
ℛ (Theorem 1(3); Corollary D's margins Φ ≥ 3/4, 7/8, 6/7 — the Step-17 (r1) numbers —
are computed exactly on "E ≥ 3 for e ≥ 2 … (and Φ_1 = 1)").
Consumer audit: the formula's only §2 consumers are Steps 5/17/18 (pole-freeness,
margins, spectral escape), all of which consume it THROUGH O-12's e ≥ 2-scoped
theorems — no consumer ever instantiates e = 1. The bug was this document's
unquantified §1 display (now quantified), not a leaf gap.
Consumes: T-8's block structure, T-3/T-6 event structure (as structure only, never
value correctness — the V6-finding-19 circularity is scoped OUT).
Delivers: the pole-free clause of (R); with Step 4, "every prime" in the root.

### Movement III — the classifier ↔ semantics dictionary (the campaign's center)

The chain touches the actual p-adic factorization semantics exactly here. The pieces
were decomposed at DELTA-2 (the K-RUN-C composition CU-1..CU-7 replacing the O-3 ⊕
O-2b joint induction; OB1/OB2/BNS/K-OB-C all EVICTED from the mandatory path — DELTA-2
§D2.4, DELTA-3 §D3.1: ZERO root-side BNS touch-points remain).

**Step 6 (O-1thr package: Theorem 1 = D-14, Theorem 2 = O-1(thr), Theorem 3 = D-15 —
per-site read locality + the cylinder law).** Statement: (Thm 1/D-14) for every
menu-LAWFUL site (H, ν), whether the canonical run on f reads (H, ν) is determined by
f's digits below the computable modulus L(H, ν) (the read ceiling) — the noncircular
quantifier form; (Thm 2/O-1thr) the realized-site two-lift tier with window closure
(K2); (Thm 3/D-15) decided ns-free verdict classes are EXACT finite unions of level-t
cylinders with the per-tree fiber scaling #Φ_N(T) = mass(T)·p^{nN} (the CYL law; owns
ALL box-level lift quantification). Proved at rev 3/4 over the sloped/sheared
convention pin (the depth-2 falsifier REFUTED the unsheared reading — 7,472 phantom
violations — and confirmed the sheared machine exhaustively, 41,720 instances, 0
violations); VAL1/KEY1/DIV1/ROOT-M/WGEO proved outright at order ≤ 1.
Status: **PROVED-UNVERIFIED** — rev 4 landed (commit 5613274; V24's REAL≡ circularity
repaired structurally: (M6c) requantified, non-ns-halt now a conclusion); pending pass
**P(O-1thr r4)** (fresh hostile pass on rev 4, owed). Displayed caveat **(E-N)** (Thm
3(c) exhaustion) is OPEN and touches CU-4.
Consumes: T-1/T-2's carry algebra (symbolic scope); the graded-presentation dictionary
= **C.1.5**, whose supplier is now DISPLAYED [REVISION 1, finding 5]: C.1.5 ("downsets
are literal digit systems") is T-2's ONE deferred proof obligation, displayed at T-2's
dual acceptance (tree §2.2) and consumed exactly here — at the mathematical machine
O-1thr's proofs run over, the dictionary is DEFINITIONAL (O-1thr §4 residue (S-1): the
clause-by-clause correspondence is displayed, and its remaining content is the S-1
machine-transcription audit, a §3.3 row that now names C.1.5 explicitly); MacLane 1936
(V1) via the LITUNIT pin.
Delivers: D-14 + D-15 to CU-1/CU-3/CU-4 and Step 17's per-box σ-constancy; the K-4/K-6
repairs route through D-15.

**Step 7 (O-2a — the upstream dictionary half: invariants, order placement,
normalization crossing, admissibility + the D-5 carrier design).** Statement: the
correspondence Θ, typed per fixed separable f from realized runs to GMN types:
(accE, accF) = (e₁⋯e_r, f₀⋯f_r) with saturation ⇔ ω = 1; certified increment nodes map
injectively to GMN orders; raw-frame side reads transport to the v_r-normalized frame;
the canonical key lifts form one GMN-admissible representative family; Theorem 2(B)/(D)
= the emitted-record ↔ GMN-datum tie; OL-6 = run decomposition + chain binding at every
level.
Status: **PROVED-UNVERIFIED** — rev 5 (commit b337195), core THRICE confirmed (V10 →
pass-2 → V25 arc; V25 on rev 4: 0 criticals, 1 minimality gap → OL-3-min trim executed);
pending pass **P(O-2a r5)**. Displayed residue: the SIX exactly-stated open lemmas
**OL-2a-1..6 = the GD-1..GD-6 families**, mapped ONE-FOR-ONE [REVISION 1, finding 5's
coverage charge]: OL-2a-1 = GD-1 (representative admissibility — §3.3 (KP)/(KPirr)
row); OL-2a-2 = GD-2 (frame/valuation tie — head CLOSED at Step 8 order ≤ 1; orders
≥ 2 = (GR-B), §3.1); OL-2a-3 = GD-3 (residual dictionary — min core CLOSED at Step 8;
FULL form at orders ≥ 2 = (GR-B), consumed by the value side); OL-2a-4 = GD-4
(engine bookkeeping — §3.3 row); OL-2a-5 = GD-5 (base-read conformance — §3.3 S-1
row); OL-2a-6 = GD-6 (run-decomposition conformance — §3.3 row, with GD-4). Every
residual has exactly one ledger home; nothing is covered twice or zero times.
Consumes: LIT-1 (GMN) via the pinned citations; the LITUNIT pins; **D-5's
carrier/equality design — supplier DISPLAYED [REVISION 1, finding 5]:** this is NOT an
external input. The tree's D-5 (WELLPOSED) carrier/equality clause is INCORPORATED as
proved content of O-2a rev 5 itself (§§1–2: the two discrete carriers, the map Θ, the
consistency predicate, Lemma R — the design the V10 → pass-2 → V25 arc audited; its
verification debt is the same P(O-2a r5)). The tree's wider D-5 semantic-invariance
clause is carried on the mandatory path by each consuming leaf's own displayed carrier
section (O-13's run-collapse well-definedness at Step 3; O-1thr's §1 machine carriers
at Step 6; CU-1's declared pins at Step 10), not consumed as a separate node — §3.3
records this disposition.
Delivers: CU-2's content (no-phantom = Theorem 2(D) ∘ ι), CU-1's base and step
vocabulary.

**Step 8 (GD23 — the GD dictionary head, GD-2 ⊕ GD-3: frame/valuation tie, development
identity, residual dictionary, over an ARBITRARY complete DVR).** Statement: (GD-2)
u_{i+1} = v_{i+1} on low-degree nonzero B; w multiplicative (MacLane); w_{i+1}(B) =
min_k(w_{i+1}(C_k) + k·γ̂_i); window polygon = N_{i+1}(f) vertex-for-vertex; emitted
record (e,h,ℓ,s,u) verbatim. (GD-3, min core) ord_{ψ̂_hom}(in(f)) = ord_ψ(R_λ(f));
(full form) R^nrm = c·R_λ(f) with slot-wise residue-field bijections — the anchored
march, restated at rev 3 in BOTH printed FGMN Thm-4.2 pairings with the exact match
verified clause-for-clause against the printed source. Stated over an arbitrary
absolutely-unramified complete DVR (killing most of D-3 by scope discipline).
Status: **VERIFIED at honest scope — leaf #4** (arc: V26 UNSOUND with order-≤1 core
confirmed → rev 2 against the LITUNIT pins → V28 SOUND-WITH-GAPS 0-critical → rev 3
(notation split + properness proviso) → pass 2 fresh Fable, 0 criticals, 9
justification gaps, commit 4d109b9 → [the wave-10 VERIFIED adjudication at d730669 was
CORRECTED AS PREMATURE at the ledger, commit 110f308] → rev 4 repairing all 9 gaps,
cores byte-stable (commit f9878d1) → GAPS-CLOSED check → **ADJUDICATED VERIFIED at the
2026-08-02 harvest** (ledger final section, commit c43b13b) [REVISION 1 status sync]).
The
honest scope IS the conditionality: order ≤ 1 proved outright; **(GR-B) at orders ≥ 2
is a DECLARED open input** (the anchored-march residue-structure package, pinned to
printed FGMN Thm 4.2 + Cor 4.4/4.8/4.9/5.6 + Prop 5.14/Cor 5.15 + MacLane Thm
10.2/Lemmas 10.1, 11.1–11.2/Thm 12.1/Cor 12.2); the (KP)/(KPirr) clauses beyond order
1 and the properness proviso at e·g = 1 refinement reads are owned by GD-1; engine
conformance (u = w for the implemented engine) is a declared non-claim (GD-4/GD-6).
Consumes: MacLane 1936 + GMN + FGMN via LITUNIT (every flag resolved MATCH; §4).
Delivers: the GD-2/GD-3 instances consumed by CU-1's step, O-9's census, O-11's K3.

**Step 9 (O-14a′ — RunRealizerExists, the upstream realizer supply).** Statement: every
coherent history's designated realizer exists (interior half from re-keyed coherence;
the (S6b′) monomial-shape clause + last-node landing flank closed at the O14ap arc).
Status: core Theorems 1–3 **TWICE-STABLE across V11/V15** (rev 3 on file); the consumed
instance RRE(p, ZMod p) is FORMALIZED Lean-core (`MovesD/R7_runRealizer.lean`,
`runRealizerExists_zmod`); listed among the CUC §0 "VERIFIED homes (no pass
condition)". The landing-flank countermodel search ran and produced no negation
(positive gates only).
Consumes [list added at REVISION 1, finding 5]: T-1/T-2's MacLane-frame vocabulary
(symbolic scope, Step 2); the coherence predicate `HistoryCoherent` — the "re-keyed
coherence" of the statement — which is the O-3 clause-3 re-key EXECUTED at DELTA-2
§D2.1 line 1 (governance on record, not an open input); MacLane 1936 via the LITUNIT
pins (§4) — **exact loci [REVISION 2, finding V2-7]: Def 4.1 (key polynomials) + Thm
4.2 (augmented values), the (V1) frame-semantics pin (LITUNIT §4, verdict MATCH)** —
consumed as the intended semantics of T-1/T-2's MacLane-frame vocabulary, the same
pins Steps 2/6 ride; NO further MacLane theorem enters O-14a′ (its core Theorems 1–3
are self-contained per the V11/V15 arc, and the consumed Lean instance rests on Lean
core only). The (S6b′) clause and the landing flank are INTERNAL — closed inside the
O14ap arc itself (rev 3), not consumed from elsewhere. The consumed instance
RRE(p, ZMod p) rests on Lean core only. The rev-3 honesty ledger's open flags
(OL-1/OL-2/(F1)) ride the NON-consumed tower strengthenings (Prop 5.4.2 sharpness,
Conjecture 5.4.C) and enter nothing here.
Delivers: CU-3's nonempty-locus witness.

**Step 10 (CU-1 — no-missing + interior adequacy + state binding; THE ONE NEW PROOF of
the K-RUN-C composition).** Statement: one ordinary induction on chain length, N-free:
for every Cons_f chain 𝐇 with N\*(𝐇) ≤ N, (i) the canonical run on f at working level
N realizes 𝐇; (ii) the engine's frame state after the realized prefix equals the stage
data of Θ(𝐇) (the OL-6 binding). Interior adequacy = per-site SPAN totality inside the
same step; ADEQ split interior/terminal with terminals routed to O5triple's counting;
no box-keyed universal statement anywhere.
Status: **VERIFIED — leaf #5** [REVISION 3 status sync, ledger 7b28562]
(arc: V27 UNSOUND, core repairable → rev 2 structural repairs (N-free induction,
interior/terminal split, construction-before-recovery, declared pins) → V29
SOUND-WITH-GAPS 0-critical → rev 3 (consumption accounting only; induction
byte-stable) → pass 2 fresh Fable, 0 criticals, 7 consumption-accounting/display gaps,
commit 252f34c → [the wave-10 VERIFIED adjudication at d730669 was CORRECTED AS
PREMATURE at the ledger, commit 110f308] → rev 4 light repairs, all 7 gaps, cores
§§1–3 byte-identical (commit 8ab8ca6) → gap-check: GAPS-REMAIN → rev 5 (commit
6299a4a, the single GAPS-REMAIN item repaired, cores byte-identical) → r5 gap-check
**GAPS-CLOSED, 0 criticals / 0 gaps** (the F-4 Lemma-R scope-note residual verified
repaired; §3/§4/SURJ spot-checks clean; commit 5329a4e) → **ADJUDICATED VERIFIED
(leaf #5) at the 2026-08-02-night harvest**, ledger 7b28562). The mathematical core
(N-freeness, creation-first, split-exhaustiveness) was confirmed by the pass-2
report; the r5 gap-check closed the accounting/display residue. Primary gate: the
depth-3 falsifier ran BEFORE rev 1 and SURVIVED.
Conditionality carried: the step consumes GD-2/GD-3(min)/GD-6 instances at orders ≥ 2
through **(GR-B)**, plus the declared pins **(P-ROOT)/(P-KEY)/(FR≡)** ((FR≡)'s
refutable order-2 content = the gate's coherent-convention finding).
Consumes: Steps 6–9 (D-14, OL-6, OL-2a-2-min/3, SPAN/(M6a)/(M6c)/VTX, REAL≡, the
realizer supply).
Delivers: the no-missing direction of realization faithfulness (K-RUN's heart); K-14
(I0)/(I1)/(I3-rc); the (FRESH) consumption site.

**Step 11 (CU-2/CU-2t/CU-3/CU-4/CU-5/CU-7 — the rest of the K-RUN-C composition;
"CUC").** Statements (per DELTA-2 §D2.3): CU-2 no-phantom = O-2a Theorem 2(D) ∘ ι;
CU-2t the terminal seam ((t-i)/(t-ii) as ONE lemma from O-2a Thm 2(B) saturation +
Cor 1.20/3.8 + TB-CAP windows); CU-3 nonempty locus (coherent form) = O-14a′ + D-14 +
(O6) — **(O6)'s supplier DISPLAYED [REVISION 1, finding 5]:** (O6) = the O3design §1
canonicalizations (branch-letter keying + deep-marker pooling), a DEFINITIONAL
bookkeeping convention for census-side counting with NO proof content (CUC §3(c)
states exactly this; the O3design record passed the V16/V21 arc) — a §3.3 pin row,
not an undefined leaf; CU-4 acceptance, selected-f (F4-S soundness at every N; F4-C
completeness at
N ≥ N\*, TB-CAP (τ-irr) perimeter-conditional); CU-5 the satellites K-OB-A/B/E; CU-7
the O5triple interface discharge ((I-1)(a,b,c) + (I-2), with the attribution correction:
the content is single-polynomial and consumes NO K-DICT-OB1).
Status: **PROVED-UNVERIFIED as a consolidation record** — wave 8 confirmed 6/7
re-labels mapped to proved homes (commit a9f294c); **CU-2t is PROVED at R3** (CUC §9,
unit D3CU2t) conditional on P(O-2a r5) + TB-CAP's D-12r perimeter + the GD residue
**including the THREE NEW GD-4 terminal rows (T-DEC)/(T-READ)/(T-VERD)** [count
AMENDED 2 → 3 at REVISION 4, folding the CU-2t R3 §9.5 touch (3)] — genuinely new
unproved mandatory-path obligations first displayed at CUC §9.4, folded into GD-4 (no
new open FAMILY) but growing the residue by three rows; the residue-count history is
stated plainly per the R3's own discipline: rev 1 billed ZERO new open inputs
(OVERSTATED, retracted at R2 per the CUC F4 correction), R2 billed TWO, and the
honest count is THREE — the R2 itself undercounted by one, the (RC-read) supply row
(T-READ) (the CU2tpass G1 finding; §3.3 GD-4/GD-6 row synced). [REVISION 3 status sync:
CUC pass 1 RAN — **UNSOUND** (b9d1d70: 1 critical,
§9.3(iii)'s Θ^τ injectivity constant in ν under an unconstrained hypothesis row, + 9
gaps incl. the (T-DEC)/(T-VERD) residue-growth contradiction; the §6.1 audit SOUND;
clauses (i)/(ii)-main survive) → **CU-2t R2 LANDED** (unit of record 567814d;
52d4eed's staging sweep captured an intermediate state: the ν-dependence critical +
its root, the undefined record-consistency predicate, repaired via the displayed
Definition RC, §§9.2a/9.3 — Θ^τ now carries ν's announced verdict pair, injectivity
restated at two displayed granularities; CU-2 rescoped to the continuing part 𝐇°;
surviving cores byte-stable; full disposition table CUC §10).] [REVISION 4 status
sync: the R2 hostile re-pass RAN — **SOUND-WITH-GAPS, 0 criticals** (4190ca4: the F1
ν-dependence repair CONFIRMED at both injectivity granularities, Definition RC
non-circular as displayed; 4 gaps — G1 the missing (T-READ) third row, G2 a (T-DEC)
row-internal contradiction, G3 the unrouted W3-carrier/2(D)-scope dichotomy, G4 (c1)
unquoted) → **CU-2t R3 LANDED** (81589e9, light: (T-READ) displayed with per-half
consumption at the §9.4 tie — the read-entry half consumes (T-READ), the verdict
half survives on (T-VERD) + clause (ii) alone; (T-DEC) SPLIT (T-DEC-dec)/(T-DEC-cor)
— corner bookings fenced to the Corollary at its own conditionality; pricing
corrected to THREE rows with the 0 → 2 → 3 history said plainly; the W3
carrier finding + 2(D)-scope dichotomy ROUTED to the O-2a owner at the P(O-2a r5)
charge — §9.5 touch (5); verified cores byte-stable); the fresh hostile pass on the
R3 record is the in-flight debt (§3.2).] The quarantined Corollary CU-2t-deep (the
GD-8 exact-key
corner) is conditional on the unpinned (REP-IRR) literature pull and is consumed by
NOTHING on the mandatory path.
Consumes (mathematical inputs): Steps 6–10 + (O6) as displayed above. The CUC §0
pending-verdict registry is METADATA — the live key the P(·) grades resolve through,
never a mathematical supplier [wording fixed at REVISION 1, finding 5].
Delivers: no-phantom + terminal verdicts + acceptance = with Step 10 the full
realization-faithfulness package (the old O-3), serving K-4/K-6's repairs, O-4's
OL1-ii, O-5, O-7's (X1)/(X4).

**Step 12 (O5triple — O-5 halt/assembly + the D-7 bijection triple).** Statement: at an
ns-free leaf of a realized run the halting verdict is the true factorization datum
((τ-hen) via LIT-3 coprime Hensel; (τ-irr) saturated leaf via OM saturation through the
dictionary); Theorem B derives D-7b LEAF-COVER from injectivity + degree checksums
alone (NO no-missing consumed — the F2′-as-assembly note, verified); D-7a
LEAF-DISJOINT and D-7c LEAF-MULT close the triple; Theorem E: any two monic separable
lifts of a decided class have EQUAL splitting types (the multiset is engine data,
lift-independent) — the σ-constancy Step 17 needs.
Status: **PROVED-UNVERIFIED** — rev 3 (commit 6fe1b2d), V23: NO criticals → rev-3
repairs 0-critical; pending pass **P(O5t r3)**, PLUS the five §2 flags
(GMN-COH)/(R-0)/(R-1)/(R-2)/(R-3) — GD-1/GD-7/GD-8 duties, NOT covered by the executed
LITUNIT. The abstract counting core is Lean-formalized (`MovesU/O5CountingB.lean`).
Consumes: Steps 7/8/10/11 via CU-7's interface; LIT-3; GMN Def 3.10/eq. (37) +
Cor 4.19 + LIT-2 defectlessness.
Delivers: correct semantic leaf labels for O-11's K1 (Step 18) and D-11's M3 (Step 17);
type(g) = typemult(T) for every lift g.

**Step 13 (O-4 + O4T — drainage: undec(k) → 0 at every prime, wild included).**
Statement, in two layers: (SEMANTIC, unconditional) the M05/V2-verified core — Lemma A
(drainage ⇔ a.e.-decidedness), Lemma C (discriminant tail bound, wild term a finite
additive shift n·v_p(n)), Lemma D (Krasner local constancy at modulus 2v+1, explicit
constant, wild-valid), Theorem E (the semantic classifier drains at rate
~p^{−N/(2(n−1))} at every prime) — plus Dfloor's SEM-DRAIN making the measure content
exact. (TRANSFER, the canonical classifier) O4T: TR-0 (a.e.-finite decision level ⇒
env → 0), FLOOR (any sound stable classifier is bounded below by the semantic one),
TR-Q (quantitative transfer under a nondecreasing UNBOUNDED majorant), and THEOREM N3:
at 2 ≤ n ≤ 3 the canonical order-≤1 classifier terminates, is sound and stable, with
the SHARP read ceiling L(f) ≤ v_p(disc f) + 1 at every prime including wild — hence
pointwise OL1 and drainage with explicit envelope, UNCONDITIONAL at n ≤ 3 (no CU/GD≥2/
BNS consumed). General n: TR-OM is CONDITIONAL on exactly the displayed seam
**(AGR) = OL1-ii** — the canonical run on each separable f terminates below a finite
N(f) with the certification predicate accepting there — assembled from CU-2 + CU-4 +
GMN Cor 4.19 (the DELTA-1 §D1.4 adjudication: this qualitative route is the MANDATORY
one; rates/O-6/O-7/O-8a are route R-QNT, struck from the root).
Status [REVISION 1 status sync]: M05 core **VERIFIED at the V2-upheld scope** (items
5–8); O4T **REPAIRED AT REV 3, AWAITING ONE FULL CLEAN PASS** (arc: V30 UNSOUND →
rev-2 repairs → Fable pass 2 UNSOUND, one localized critical: Corollary N3-BRACKET's
terminal "=" false for N ≥ 2 by the level-normalization factor p^{n(N−1)}, plus 4 gaps
(import inventory short: Galois descent + char-0 separability) → **rev 3** (commit
bb4326c): the terminal "=" → "≤" with the exact p^{n(N−1)} normalization identity
displayed and the verifier's 8-vs-32 refutation shown, the density form kept as the
identity-bearing statement (§4 consumed only the inequality — nothing downstream
consumed the false clause); import inventory COMPLETED to eight named Facts — Facts
**SEP** (char-0 separability of irreducibles) and **DES** (Galois descent/fixed field)
added as in-line-proved imports with consumption-site cite tags, six-vs-eight
reconciled (EF/GRD each bundle two of V30's items); the every-lift-separability chain
displayed in N3's proof; cores byte-stable (diff-verified). The repair was CHECKED
CLEAN at the 2026-08-02 harvest (ledger, c43b13b), but one full clean hostile pass is
still OWED before any VERIFIED grade; the mathematical core has now survived
line-by-line audit twice. [REVISION 3 status sync: pass 3 (the acceptance pass) RAN —
**SOUND-WITH-GAPS, ZERO criticals** (ed413ae; harness independently re-run, 2.53M
classes, ceiling sharpness confirmed; all 11 charges PASS), two one-line gaps (the
(I1) base-case "≥ 1" criterion display — the consumed form verified correct — and the
"one external import" undercount vs M05 Lemmas B/D) → **r4 (the two one-liners)** —
**LANDED at revision close** (3956500: the (I1) criterion corrected "≥ 1" → "> 0"
with the verifier's derivation displayed; the external-import count corrected to
three with exact consumption sites; cores byte-stable) — **+ one confirming pass to
the bar** (ledger 7b28562); the core has now survived line-by-line audit three
times.] [REVISION 4 status sync: the confirming pass (pass 4, acceptance) RAN —
**SOUND, CLEAN PASS: 0 criticals / 0 gaps** (8602e97: all 12 charges + acceptance
items pass; the core independently re-derived including both CEIL corners; harness
re-run digit-for-digit vs the sealed JSON) → **O4T ADJUDICATED VERIFIED (leaf #7)**
at the confirming-passes harvest (ledger 85670f7); the "REPAIRED AT REV 3, AWAITING
ONE FULL CLEAN PASS" header above is SUPERSEDED — the M05 core's V2-upheld grade
stands unchanged.]
Consumes: Steps 1/10/11 + GMN Cor 4.19 + the O4T import inventory (§4).
Delivers: the undec(k) → 0 clause of (SQ) = the SEMANTIC layer — unconditional at
every n and every prime (Theorem E + Lemma A/C/D, with Step 1's SEM-DRAIN making the
measure content exact); since §1's undec(k) is DEFINED semantically, this is all
clause (SQ) consumes [attribution corrected DOWNWARD at REVISION 4, finding VC4-4 —
the former line's "(AGR)-conditional at general n" priced the TRANSFER layer into
(SQ)]. The TRANSFER layer (the canonical classifier's own termination + drainage:
unconditional at n ≤ 3 by Theorem N3; conditional on (AGR) (= CU-2 + CU-4 + Cor
4.19, all on file above) at general n) serves the classifier-side counting reading
consumed by Step 19's squeeze machinery inside clause (R)'s conditional scope, and
the algorithmic-decidability strengthening — NOT clause (SQ)'s statement.

### Movement IV — the value side (the tables evaluate correctly)

**Step 14 (O-9 — the order-r stratum census).** Statement: for a type of order r the
order-(r+1) stratum census over O/π^N is one ℕ-valued polynomial in q per stratum,
independent of p, O, δ (census field degree d = f₀⋯f_r — the DELTA-3 §D3.2 index fix
governs). Level-1 (order-1 strata, every n, every prime power, every complete DVR) is
PROVED (M08 Theorem 2, 46-strata machine check). Order ≥ 2: REDUCED to exactly TWO
pre-existing named opens — **(GR-B)** (enters as the anchored-march residue structure;
CEN-W conditional on it alone) and **(FRESH)** (the joint-with-parent separation
clause; CEN-J = THE census). TYPE-MARCH (+ the F₃ type-breaking countermodel) shows the
march is what MAKES the census polynomial: GD-3-FULL is a theorem-level dependency of
the value side. OL-A's ledger (A1/TRI/LED/(DET)) proved outright; OL-B discharged to
GD-3 per DELTA-2.
Status [REVISION 1, finding 4 + status sync]: **REPAIRED AT REV 2, RE-PASS OWED.**
Verify pass 1 NOT ACCEPTED (commit c17777f; 2 criticals: the census exponent E′'s
left-tail ceiling REFUTED by machine countermodel (256 vs 64 — overcount q^d per
integral left-tail slot), and JUNCTION-PIN's PROVED label unsupported; the verifier's
own sound-list: TYPE-MARCH + F₃, A1/TRI/LED, (DET), CEN-W's (GR-B)-only conditionality
— the reduction's SHAPE survives). The pass-1 verdict made the then-current [V] filing
DISHONEST (finding 4 is accepted: a refuted exponent is a missing proof, not a
verification debt). **The repair has since LANDED — rev 2, commit 01c21e6:** E′'s left
tail made STRICT (floor(line)+1; the countermodel now predicted exactly, 64 = 64), the
K5 predict-from-ledger falsifier added (11/11 cells exact; the rev-0 formula refuted
at every integral-left-tail case), E″ displayed and validated against M08 at r = 0, an
**(ADM)** admissibility hypothesis displayed (an explicit hypothesis on CEN-W/CEN-J,
now a §3.1 [M] row carried by (ROOT-C)(H3) [REVISION 2, finding V2-5]; the r2's
"automatic at orders ≤ 1" claim is SUPERSEDED — twice rescoped, see the r3/r4 syncs
below; the single operative definition is the §3.1 row's FULL-attainment form
[REVISION 4, finding VC4-2]), and JUNCTION-PIN's
PROVED label WITHDRAWN — honestly rescoped as OPEN, absorbed into **(FRESH) as its
clause (c)** (the telescope consequence is proved GIVEN the clause). The sound-listed
core is byte-stable. With the repair on file the row is again honestly [V]:
re-pass owed. [REVISION 3 status sync: the re-pass (pass 2) RAN — **UNSOUND** (1
critical, 3 gaps; af2293e): both pass-1 repairs (strict left tail, junction-pin
rescope) verified SOUND, but the rev-2 (ADM) display rests on a FALSE class-vs-value
attainment equivalence (r = 1 countermodel: e₁ = 3, h₁ = 2, weights {0,2,4}, on-line
β = 1 unattained — empty stratum, positive formula; the automaticity claim refuted at
that reading); K5 + harness records verified log-exact → **r3 with the VALUE-attained
(ADM) reading** (ledger 7b28562) — **LANDED at revision close** (460ea59: automaticity
rescoped r = 0 automatic / r = 1 displayed decidable inequality / general r ≥ 1
withdrawn; LED-top(ii) image-subspace fix; K6 falsifier 0 = 0 exact); pass 3 owed.
The §3.1 (ADM) row carries the matching note.] [REVISION 4 status sync: pass 3 on r3
RAN — **UNSOUND, 1 critical** (b7df5c2: the attainment ladder goes one rung deeper —
VALUE-attainment (dim G_{β_k} ≥ 1) is insufficient at PARTIALLY attained slots; the
count needs FULL attainment dim G_{β_k} = d; machine countermodel from the note's own
LED-top(ii) type: r = 1, d = 2, CEN-W display 73728 vs truth 49152 at q = 2, ratio
(q+1)/q per partial slot — every prior value gate ran at d = 1 where the notions
coincide; all four charged r3 repairs + the census layer verified clean) → **r4 with
(ADM) at FULL attainment LANDED** (unit of record 35faac7, draft captured at
e8e1839/031784c: dim_{F_q} G_{β_k} = s(β_k+1) − s(β_k) = d, still p-free per-datum
decidable; the r = 1 inequality re-derived for the FULL predicate
β_k ≥ h₁((h₁^{−1}β_k mod e₁) + (f₁−1)e₁), collapsing to r3's at f₁ = 1; the r3
"(GR-B) bijection of F_{r+1}" gloss WITHDRAWN — read injective on G_β with image V_β,
onto ⟺ FULL, propagated to §§5.1/6.3/6.4; automaticity: r = 0 STILL automatic
(dim = f₀ = d); K7 falsifier ALL PASS — the countermodel refuted + the FIRST d ≥ 2
VALUE gate exact, census q^14(q²−1)² at p ∈ {2,3}); **pass 4 in flight**. The §3.1
(ADM) row is rewritten to this single operative form at REVISION 4, finding VC4-2.]
Consumes: Step 8 (GD-3), GMN Prop 2.7/Lemma 2.2/Defs 2.19–2.21 via pins.
Delivers: the transition weights of T-7s's tables as proven counts — K3's census half
for Step 18.

**Step 15 (O-10 — sibling independence at adapted cells; K-COUNT).** Statement, sharper
than charged: in factor coordinates over ℤ_p, the fibers of the level-N multiplication
map over a ρ-separated polydisc are constant and nonempty at EVERY N ≥ τ, of size
p^{Σ min(e_i, N−τ)} (Smith profile), = p^ρ exactly in the D-8 guard range N ≥ τ + e_max;
Theorem 2 = the adapted-cell (SIB) product law, UNCONDITIONAL in factor coordinates;
K-JAC = Lemma 3; OL-4/D-8r RESOLVED (no small-N anomaly). Application to the engine's
realized site strata is conditional on the two displayed interfaces **K-LOC** (= M07
OL-3) and **(I-τ)** — both priced into the GD families.
Status: **VERIFIED at scope — leaf #6** [REVISION 3 status sync, ledger 7b28562]
(commit 3e9f199; pass 1 CLEAN, ec5e9a1: 0 criticals, 0 load-bearing gaps; pass 2
model-diverse SOUND-WITH-GAPS, 5296528 — all five charged proofs check, Lemmas 1/2
verified incl. the adversarial minor case, harness 68/0 reproduced; 2 justification
gaps: the D-8 value-vs-law split collapses definitionally (fix rides the next doc
touch) + one undisplayed box-count transport cite → **ADJUDICATED VERIFIED (leaf #6)
at scope** at the 2026-08-02-night harvest; the two gaps were repaired at r2, landed
at revision close (3956500) — VERIFIED stands per the wave-14 ledger, framing fixed).
Falsifier: `verification/o10_kcount_harness.py` 68 PASS / 0 FAIL, predictions sealed
pre-run.
Consumes: LIT-8c (Sylvester/resultant); GMN stage factorization **K-FACT — pinned
[REVISION 1, finding 8]: K-FACT = GMN Thms 1.15/1.19 + Thms 3.1/3.7** (the recorded
perimeter, `docs/GMN_citations.md`; the O-10 §8 honesty ledger consumes exactly this
citation set — all four loci already in the §4 GMN pin list).
Delivers: K1's product law for Step 18; T-6's (SIB-STEP) at the statement layer.

**Step 16 (O-8b + D-3 — the unramified-base package; clause (UB)).** Statement: the
root's "same R_τ at q = p^δ" clause. Route (adjudicated at GD dispatch): the GD
families and O-9 are stated over an ARBITRARY absolutely-unramified complete DVR from
the start (Steps 8/14 — GD23's generality audit V26-confirmed: no proof uses
completeness, perfectness, or a Teichmüller section), collapsing D-3 to per-leaf scope
hygiene PLUS the alphabet slice O-8b: at δ-stable position classes the re-based slot
map is F_{p^δ}-linear and a_δ = δ·a₁ — M14's conditional proof over the displayed
(R1)–(R4) (the T-1 stage laws re-proved verbatim over O_δ = W(F_{p^δ})).
Status: GD23's arbitrary-DVR scope **VERIFIED** (inside leaf #4); O-8b
**PROVED-UNVERIFIED conditional on (R1)–(R4)** (M14's conditional proof is ON FILE;
the (R1)–(R4) base itself is the unwritten-but-expected-mechanical §3.1 row); pending
pass **P(O-8b/M14)**, now a named §3.2 row [REVISION 3, finding B2 — it was the one
consumed PROVED-UNVERIFIED proof with no ledger row naming its pass]; N8 numerics
exhaustive (199,723 alphabets, 17 fields, 0 violations).
**Honest scope of what this step proves [REVISION 1, finding 7]:** (i) the GD/census
layers (Steps 8, 14) hold over an arbitrary absolutely-unramified complete DVR —
proved/stated at that generality from the start; (ii) the alphabet law
(F_{p^δ}-linearity of the re-based slot map + a_δ = δ·a₁) AT δ-STABLE POSITION CLASSES,
conditional on (R1)–(R4). This does NOT yet derive the theorem's global clause (UB):
missing are exactly (a) the per-leaf O_δ re-base audit for the leaves stated over ℚ_p
(the dictionary/CU/drainage layers — the "per-leaf scope hygiene" of the D-3 collapse,
declared but unwritten), (b) that δ-stable position classes exhaust the classifier's
realized ledger at every δ, and (c) that the full solve + type aggregation commute
with unramified base change. (a)–(c) = the displayed row **(UB-X)** in §3.1; clause
(UB) of (ROOT-C) is conditional on **(H1)–(H3)** (inherited through this step's
Consumes-list: Step 8 is (GR-B)-conditional at orders ≥ 2, Step 14's census is
(FRESH)/(ADM)-conditional at orders ≥ 2, and the (UB-X)(a)-transported
dictionary/CU/drainage layers carry D-12r/(E-N) — none of these evaporates over O_δ)
**+ (H4a) = (R1)–(R4) + (H4b) = (UB-X) + (H5) = (PACK)** (the actual-pack
correspondence, inherited through the transported evaluation chain — the value tie
at q^δ runs through Steps 17/18/18b's pack consumption; added at REVISION 4, finding
VC4-3), exactly as §1 now displays [attribution
completed at REVISION 3, finding B1]. [REVISION 2, finding V2-2: (R1)–(R4) is NOT
(UB)-only — it also enters
clause (R) through Step 18's K3-c; the split (H4a)/(H4b) records this.]
Consumes [list added at REVISION 1, finding 5]: Step 8 (the arbitrary-DVR GD
statements + the V26-confirmed generality audit), Step 14 (the census over any
complete DVR), Step 2 (the T-1 stage laws as the re-proof template for (R1)–(R4)),
M14's conditional proof (the O-8b attempt on file), and the §3.1 rows
(R1)–(R4)/(UB-X). N8 is a flag, never a substitute.
Delivers: clause (UB) at the displayed conditional scope.

**Step 17 (D-11 first tranche — MASS-ID M1/M1′/M3: the pack side; the instance pin).**
[REVISION 1, findings 2/11: D-11 is STRATIFIED. Its M2 clause consumed (S2) = the
O-11 composition datum while O-11 consumed D-11's pack side — a genuine cycle as
originally displayed. The honest order is **D-11 {M1, M1′, M3} ≺ O-11 ≺ D-11 M2**, and
the steps now follow it: this step carries ONLY the first tranche; M2 is Step 18b.]
Statement: (M1, one-step) every solve entry of 𝔅_n at every prime power IS the Haar
mass of its continuation event — Σ = 1 across each row now a THEOREM; a.s. termination
from the (r1) margins reread as termination margins — UNCONDITIONAL over the VERIFIED
O-12 lemma base (L1–L6′). (M1′) the (O2) verdict-row coarseness finding (gate object,
not a density carrier). (M3) row labels are true types: σ-constancy across one
continuation event's cylinder ← O5triple Theorem E + D-15 (per-box lift uniformity) —
NO ∼_OM/OB2 consumption (the DELTA-3 §D3.1 audit, re-confirmed constructively by this
unit; zero root-side BNS touch-points). OL-O12-2's mathematical half CLOSED here.
Status [REVISION 1 status sync]: **PROVED-UNVERIFIED, r2 owed** (attempt landed,
commit 0cae7d8; wave-10 adjudication: "THEOREM M1 PROVED UNCONDITIONALLY over the
VERIFIED O-12 lemma base"; verify pass 1 NOT ACCEPTED as billed, commit 2587c70 — 1
critical: M1(c)'s MULTI-BLOCK a.s.-termination billing consumes open (S1) while
ledgered unconditional (per-block survives unconditional; contained), + 3 gaps; M1(a,
b,d), the (O3) resummation, and the uniqueness pivot SURVIVE → D-11 r2 owed).
[In-flight at REVISION 1 close: **r2 LANDED**, commit 566b967 — the critical contained
exactly as specified (M1(c) rescoped to per-block unconditional content; multi-block
a.s. termination MOVED to Lemma M2.0 at M2's (S1) layer; the (O2′) balance leg
DERIVED; a THIRD seam **(S3)** = the projective assembly weight DECLARED, owner annex
A-1, monic scope pinned on M2's statement); pass 2 launched.] [REVISION 3 status
sync: pass 2 (V31) RAN — 2 criticals, both CONTAINED at **r3** (8a0786c: M1(a)
rescoped to families (i)–(iii) with displayed exclusions; the completed-node
overclaim WITHDRAWN — status honestly LAYERED, clause 4 = the actual-pack
correspondence OPEN as cited; Lemma M2.0 rewritten over countable symbolic
addresses); pass 3 owed.] [REVISION 4, finding VC4-3: the OPEN clause 4 is now a
LEDGER ROW — the §3.1 [M] row **(PACK)**, carried by (ROOT-C)(H5): what Steps 18/18b
consume of this step is the M1/M1′/M3 layers at their displayed conditionality PLUS
that correspondence, and the correspondence has no proof on file — it cannot ride
the §3.2 D-11 [V] row (a pass-debt class requires a proof on file), so it is priced
as hypothesis-grade open mathematics.]
Falsifier: N6-regp-ext2000, 303/303 primes < 2000, all EMPTY, margin sharp at 6/7.
Consumes: Step 5's lemma base (as the mass statements they are), Step 6 (D-15), Step
12 (Thm E), T-3/T-6 mass laws. NOTHING from Steps 18/18b.
Delivers: the pack-side mass laws + true row labels that Step 18's K1/K2 consume;
D-9k's escape input at the pack; the (r1) uniqueness pivot Step 18b re-uses.

**Step 18 (O-11 — SERIES-TIE: per-τ tree series = R_τ).** Statement — displayed
exactly, since Step 19's attribution rides on it [REVISION 1, finding 11]:

    (O-11)  for every type τ: the σ-graded tree series of T_can, assembled at the
            intended 𝔅_n instantiation, EQUALS the block-solve value R_τ in ℚ(q).

This is the SERIES = SOLVE-VALUE tie ONLY — it does not by itself say any Haar density
equals anything (that is Step 18b). Proof: the M04 Theorem-4 walk (least fixed point,
Bekić triangularization, Neumann under spectral escape; proved self-contained)
re-priced at the D-9 corrected dependency set: K1 ← O-10 (guarded) + (I-τ)→GD + CU
leaf labels; K2 ← O-12 at 𝔅_n + D-11 PACK SIDE (= Step 17's tranche, never M2) + the
**(PACK)** correspondence (§3.1, = (ROOT-C)(H5): that the concrete assembled pack IS
the intended 𝔅_n instantiation entry-for-entry — Step 17's OPEN clause 4, consumed
here and at Step 18b as the identification the tie evaluates through [REVISION 4,
finding VC4-3]); K3 =
[1v]-FULL value correctness ASSEMBLED from T-7s + O-9's census + O-8b (arbitrary-DVR);
K4 ← Dfloor/D-15/CU mass semantics. Every consumption displayed (the unit's 20-row
table). δ-stable interface note [REVISION 3, finding A5; PRICED at REVISION 4,
finding VC4-1]: O-8b's law is declared AT
δ-STABLE position classes only (Step 16), and that K3-c's realized δ > 1 pools are
δ-stable position classes is a match ASSERTED at the D-c interface (O-11 r2/r3's
declared row) with NO proof or [V]/[T] row supplying it. It is therefore no longer
carried as a presumption inside (H4a): the fragment is NAMED **(K3-δ)** = (UB-X)(b)
restricted to K3-c's realized pools, and clause (R)'s displayed attribution now
CONSUMES it ((H1)–(H3) + (H4a) + (H5) + (K3-δ) — §1; the joint five-hypothesis
theorem is unchanged since (K3-δ) ⊆ (H4b)). A direct match display (or a re-scope)
rides the next O-11/O-8b touch and would return clause (R) to (H4a)-only at this
interface.
H.6 fence display [unit TREE-GAPS, audit gap G-4]: K3-a consumes T-5's H-DOMAINS
package at its VERIFIED-DUAL perimeter, whose named open kernels are the tree T-5
row's six H.6 fences (XHD-d-EX(∂), M4b-T-AUD, U-R-COUNT, XHD-u-X, H-LIST-GEN, E-POS —
roster with owners/refuters at `ASSEMBLY_PLAN_2026-07-26.md` REV 15/16). The tree's
"six fences gate [1v]-FULL" line is SUPERSEDED AS ROUTED by the O-11 r2/r3
restructure (K3-a, the G-5 repair): NO fence is consumed here as an open general
lemma — the ROOT-consumed residue is the SINGLE condition that the built per-n tables
sit INSIDE the fenced perimeter, proved nowhere at general n (V-n3 178/178 / H-n3
151/151 are sealed n = 3 evidence), = D-11's restated-charge item (vii), carried at
the §3.3 widened-charge row (acceptance owed by the D-11 owner). No (ROOT-C)
hypothesis is affected: the condition rides D-11's PENDING tier-1 grade (Steps
17/18), not (H1)–(H4b); if a built pack ever NEEDS fenced territory (sharpest:
H-LIST-GEN's beyond-(TRI) partitions), the fence kernel so touched becomes consumed
open mathematics — an escalation the §3.3 row displays. [Concurrency sync: REVISION 4
(in flight at this unit's close) adds hypothesis (H5) = (PACK), D-11's open clause 4
(the actual-pack row correspondence, finding VC4-3) — a DIFFERENT D-11 clause: item
(vii) is the H-fence conformance of the built tables, not the pack↔𝔅_n row
correspondence, and remains carried by the widened-charge row, not by (H5); whether
it too should be promoted to hypothesis grade is flagged to the next VC pass at the
§3.3 row.] Full adjudication + the fence-by-fence mapping table: tree DELTA 4 §D4.2.
Status [REVISION 1 status sync]: **PROVED-UNVERIFIED (ASSEMBLED), r2 owed** — commit
3fc8f52; tier-1 residue exactly **{(GR-B), (FRESH), CU-2t, D-11 first tranche}**;
verify pass 1 NOT ACCEPTED AS STATED (commit a7ede72 — 1 critical: (M6b)(iii) consumed
at K4-CYL/row 4 but priced into no tier, so the "exactly FOUR" residue display is
unsupported as written, + 8 gaps incl. reductions asserted by pricing-citation; the
equivalence directions and the walk itself CLEAN; drainage verifiably unconsumed) →
O-11 r2 owed. [In-flight at REVISION 1 close: **r2 LANDED**, commit 1bd8bd1 — the
"exactly FOUR" display withdrawn, restated as the tier-1 four + THREE DECLARED
interface rows with ledger homes HERE: **D-a** = (M6b)(iii)+(ii−) → the §3.3
GD-4/GD-6 row; **D-b** = (I-τ)/K-LOC → the §3.3 interface row; **D-c** = (R1)–(R4) →
the §3.1 [M] row (= (ROOT-C)(H4a) since REVISION 2: through K3-c this row conditions
clause (R) itself, not only (UB) — finding V2-2); V1 corrected to the ENGINE-PROXY
form; NEW supplement
`o11_v2_oracle_pin.py` (10/10, engine ≡ oracle as rational functions) closes the
executed-vs-sealed gap; pass 2 launched. The r2's §9 owed ROOT touches are EXECUTED
in this document — see §7.] [REVISION 3 status sync: pass 2 (V32) RAN — billing
precision items → **r3** (7aef1b9: tier 2 SPLIT into hypothesis-grade rows H-1
((ADM), consumed at K3-b) / H-2 (D-12r) / H-3 (the O5triple five flags) / H-4
(LIT-1), the "nothing in tier 2 adds an open lemma" claim WITHDRAWN; §7.1 oracle-pin
premises displayed; walk/cores byte-stable); pass 3 owed.]
Falsifier ran FIRST: `verification/openmath/o11_seriestie_check.py`
including Finding F1's test at the real-pack proxy (the n = 2 solve reproduces the
true triple identically in ℚ(q); n = 3 five types symbolic; monotone bracket
exhaustive p = 2, 3, 5; the pass-1 record corrects the count to 37/37 live).
Consumes: Steps 1, 5, 6, 10–12, 14, 15, 16, 17 — all EARLIER. NOT consumed: D-11 M2
(Step 18b) — the cycle is gone by stratification, not by fiat.
Delivers: the series = R_τ half of clause (R)'s evaluation.

**Step 18b (D-11 second tranche — MASS-ID M2: the density IS the series).** [NEW STEP
at REVISION 1, findings 2/11.] Statement:

    (D-11 M2)  for every type τ: α(n, τ; p) — the Haar density of clause (0) — equals
               the σ-graded tree series of T_can; equivalently, the solved values are
               the real conditional densities.

Proof: the D-11 M2 argument (commit 0cae7d8) with its two seams now supplied by
EARLIER steps: **(S1)** = the GD-3-FULL/O-9 residual-descent hand-off ← Step 14 (+ its
(GR-B)/(FRESH)/(ADM) conditionality, §3.1 — the census is consumed at its full
displayed hypothesis set; the former "(GR-B) conditionality" summary omitted the
other two inherited rows [(ADM) added at REVISION 4, finding VC4-5 — a local
consumer-accounting fix; the root-level clause-(R) attribution already included
(ADM)]); **(S2)** = the O-11 composition datum ← Step 18. (r1) is
the uniqueness pivot (Step 17). With Step 18 this closes the chain
α = (tree series) = R_τ — as an identification of the CONCRETE pack's densities with
the solve values, conditional also on **(PACK)** (§3.1, (ROOT-C)(H5)) through the
Step 17/18 consumption [REVISION 4, finding VC4-3].
**Scope: MONIC — and the third seam (S3) is NOT consumed here [REVISION 2, finding
V2-1].** M2's stated conclusion is about the monic ensemble — exactly clause (0)'s μ
(monic degree-n ≅ ℤ_p^n), which is all this walk needs. D-11 r2's third seam **(S3)**
(the mass reading of the projective assembly weight (q−1)/(q^{n+1}−1), owner annex
A-1) conditions ONLY the PROJECTIVE reading of M2's conclusion, per the r2's own
scoping ("M2 as stated (monic ensemble) does not consume it"; its §3 seam display and
Theorem M2's bracket) — and no §2 step consumes that reading: the projective
normalization is ANNEX by standing directive (§1 "Relation to the tree's root").
Step 5's pole-free claim covers the weight as a RATIONAL FUNCTION ((g2) of the O-12
grammar); its mass reading enters nowhere on the mandatory path. The proof above
therefore names (S1), (S2), (r1) and nothing else — correctly, not by omission.
Status: **PROVED-UNVERIFIED, r2 owed** (same D-11 record and pass-1 verdict as Step
17; the M2-specific pass-1 gap — the (O2′) balance-equation leg underderived — rides
the r2).
Consumes: Steps 14, 17, 18 — all earlier; the (GR-B)/(FRESH) rows through (S1).
Delivers: the α = series identification; with Step 18, the α(n,τ;p) = R_τ(p)
evaluation clause of (R).

### Movement V — the closer

**Step 19 (T-U + K-13 + O-12 — the squeeze fires at every prime).** THEOREM U
(VERIFIED-DUAL, conditional on its displayed §U.SQ.6 kernel ledger — ASSERTED to
coincide with the Steps 1–18b roster plus the recorded evictions/annex items; the
row-by-row correspondence is NOT displayed here and is honestly carried as a §3.3
audit row [REVISION 3, finding A8]) takes: the bracket at every finite level (Step 1
+ D-15 + T-6 — of these, clause (SQ)'s SEMANTIC bracket is Step 1's ALONE,
unconditional; the D-15/T-6 legs serve the classifier-side counting tie inside the
evaluation chain, at clause (R)'s conditionality [re-attributed at REVISION 4,
finding VC4-4 — this supersedes the REVISION-3 A6(ii) phrasing "the (SQ) bracket
consumes T-6"]), drainage
(Step 13 — the SEMANTIC layer, unconditional; the classifier-transfer layer likewise
rides the evaluation squeeze, not (SQ) — finding VC4-4), the evaluation chain —
**attribution exact [REVISION 1, finding 11]: Step
18 delivers series = R_τ (O-11); Step 18b delivers α = series (D-11 M2); TOGETHER they
deliver α = R_τ — neither alone does; the chain carries (H4a) = (R1)–(R4) through
Step 18's K3-c (the base-changed β-legs) [REVISION 2, finding V2-2], the (K3-δ)
fragment of (H4b) at the same interface [REVISION 4, finding VC4-1], and (H5) =
(PACK) through Steps 17/18/18b's pack consumption [REVISION 4, finding VC4-3]** —
and the
pole-free specialization at every prime power (Steps 4 + 5 + 17; every self-loop
denominator at e ≥ 2 by Step 5's (SL≥2) display [REVISION 2, finding V2-6]) — and
squeezes: decided_τ(k)/p^{nk} → R_τ(p) = α(n,τ;p)
at EVERY prime including wild. **Σ_τ R_τ = 1, concluded HERE [REVISION 3, finding
B3]:** Step 1 supplies Σ_τ α(n,τ;p) = 1 at every p plus the interpolation principle;
Steps 18 + 18b supply α(n,τ;p) = R_τ(p) at every p (conditional on (H1)–(H3) + (H4a)
+ (H5) + (K3-δ),
already inside clause (R)'s displayed scope); hence Σ_τ R_τ agrees with 1 at
infinitely many prime powers, and Σ_τ R_τ = 1 in ℚ(t) — no new hypothesis; the former
attribution "from Step 1" over-credited the VERIFIED leaf beyond its declared
statement. Clause (UB) from Step 16
at its displayed conditional scope ((H1)–(H3) + (H4a) + (H4b) + (H5) — completed at
REVISION 3, finding B1, and at REVISION 4, finding VC4-3). This is exactly (0) + (SQ)
+ (R) + (UB-conditional): **(ROOT-C)**, quantifier-for-quantifier. ∎ (conditional
exactly on the (ROOT-C) hypotheses (H1), (H2), (H3), (H4a), (H4b), (H5) — attribution
per clause displayed at §1, with clauses (0) and (SQ) UNCONDITIONAL [REVISION 4,
finding VC4-4]; the §3.2/§3.3 rows are audit debts on
the composition, displayed, not hypotheses)

**Composition audit trail (rewritten at REVISION 1).** Acyclicity, edge-checked: Step
1 consumes no later node (the former T-6 attribution re-pointed to its own Appendix A
— finding 1); Steps 2–5 are symbolic/regularity and consume only earlier steps (B-1..
B-7 grades displayed at Step 2 — finding 3); Steps 6–13 form the DELTA-2 recut order
(the O-2/O-3 cycle decomposed into O-2a upstream + the CU composition; OB1/OB2
evicted), with every formerly implicit input now displayed (C.1.5, D-5, (O6), Step-9
Consumes — finding 5); Steps 14–18b consume only earlier steps, with the former
D-11/O-11 cycle stratified as 17 ≺ 18 ≺ 18b (finding 2); Step 19 consumes 1–18b. The
V6 completeness review (26 findings) and the V5/V16/V21 architectural rejections were
each dispositioned in the tree's DELTAs; every countermodel on record is explained by
the repaired statements and none touches the root (tree §2.3 consistency note); VC1's
composition findings are dispositioned in §7.

---

## 3. THE CONDITIONALITY LEDGER (everything the root rests on beyond literature)

The complete honest list, per the wave-10 residue enumeration (ledger §"WAVE 10 +
PASS-2 ADJUDICATIONS": "THE WHOLE MANDATORY-PATH RESIDUE now = {(GR-B) orders ≥ 2
(FGMN-pinned, transcription), (FRESH), the O-9 repair, O4T pass 2, D-11/O-11
verification cycles, ROOT ASSEMBLY}" — quoted as of wave 10; the rows below are SYNCED
to the 2026-08-02 harvest at REVISION 1), EXPANDED to every named pin/flag a reader of
§2 encounters. Character classes: **[V]** verification-pass debt (a proof is on file; a
named fresh-context hostile pass is owed — no new mathematics expected unless the pass
finds some); **[T]** transcription debt (content pinned to printed sources or existing
proofs; writing/auditing owed, no new mechanism expected); **[M]** genuine open
mathematics (no proof on file). The CUC §0 pending-verdict registry
(`lean/notes/openmath/CU_cluster_phaseB.md` §0) is the live key for the P(·) items.

### 3.1 Genuine open mathematics [M] — the honest mathematical distance

| item | statement | owner | notes |
|---|---|---|---|
| **(GR-B) at OM orders ≥ 2** | the anchored-march residue-structure package (GD-2/GD-3's one open input): the frame tie + residual-dictionary march at orders ≥ 2, modeled on printed FGMN Thm 4.2 (both pairings), with the properness proviso | GD-1/GD23 arc (verify passes: the GD23 verification cycle continues at orders ≥ 2) | order ≤ 1 PROVED over an arbitrary complete DVR (inside VERIFIED leaf #4); the wave-10 ledger grades the ≥ 2 layer "FGMN-pinned, transcription" — every target statement is pinned to a printed theorem (LITUNIT §7), but the composed march at ≥ 2 is unwritten: honestly [M] until written and passed. Enters Steps 10 (CU-1's step), 14 (CEN-W), 16, 18 (K3), 18b ((S1)) |
| **(FRESH)** | the joint-with-parent level-determinacy separation clause (O-9's named open), priced at the GD-2/CL-13 vertex-law layer = CU-1's step content; **since the O-9 rev-2 repair it carries clause (c) = the former JUNCTION-PIN** (PROVED label withdrawn at 01c21e6; the telescope consequence is proved GIVEN the clause) [REVISION 1, finding 4] | O-9/CU-1 layer | enters Step 10 (CU-1's step — the GD-2/CL-13 vertex-law layer where it is priced; Step 10's Delivers-line names the consumption site, so clause **(R)** inherits it through Step 18's K1/CU leaf labels — the REVISION-3 A6(iii) phrasing "clause (SQ) inherits it" is SUPERSEDED at REVISION 4, finding VC4-4: the semantic (SQ) is unconditional and consumes no CU content) and Step 14's joint census CEN-J, hence Step 18's K3, and Step 16/clause (UB) through the same census (REVISION 3, finding B1). Numerically unviolated (8.2M boxes) |
| **(R1)–(R4)** (O-8b's base) **= (ROOT-C)(H4a)** [re-scoped at REVISION 2, finding V2-2] | the T-1 stage-tower laws re-proved verbatim over O_δ = W(F_{p^δ}) | O-8b (M14's conditional proof closes given them) | expected mechanical ("nobody has written it" — tree O-8b); N8 exhaustive. Borderline [M]/[T]; kept here for honesty. Enters Step 16 AND Step 18 (O-11 K3-c — declared row D-c at O-11 r2): NOT clause-(UB)-only — through K3-c it conditions clause (R)'s α = R_τ evaluation wherever verdict rows consume base-changed β-legs (δ > 1 pools). Audit note [REVISION 3, finding A5; PRICED at REVISION 4, finding VC4-1]: O-8b's law is declared at δ-STABLE position classes; that K3-c's realized δ > 1 pools are of that kind is asserted at the D-c interface with no supplying row — so the presumption is NO LONGER carried inside (H4a): the fragment is named **(K3-δ)** (= (UB-X)(b) restricted to K3-c's realized pools, displayed on the (UB-X) row) and clause (R)'s attribution consumes it explicitly; the match display (or a re-scope) rides the next O-11/O-8b touch and would retire (K3-δ) from clause (R) |
| **(ADM)** — O-9's census admissibility [NEW row at REVISION 2, finding V2-5; REWRITTEN to the single operative form at REVISION 4, finding VC4-2] | **THE OPERATIVE DEFINITION (O-9 r4, FULL attainment):** every on-line lattice slot's β_k is FULLY attained by the ledger — dim_{F_q} G_{β_k} = s(β_k+1) − s(β_k) = d, equivalently #{𝐣 : wt(𝐣) ≡ β_k (mod e), wt(𝐣) ≤ β_k} = d — the explicit hypothesis on CEN-W/CEN-J (O-9 r4, unit of record 35faac7). Two earlier displays are REFUTED and superseded, kept here so no reader can consume them: the r2 CLASS form "β_k mod e ∈ {wt(𝐣) mod e}" (refuted by K6's r = 1 countermodel, 256/26244) and the r3 VALUE form "G_{β_k} ≠ 0" (refuted at d ≥ 2 by the pass-3 countermodel, 73728 vs 49152, ratio (q+1)/q per partially-attained slot) | O-9 (Step 14) | p-free and per-datum DECIDABLE (a finite lattice check; at r = 1 the displayed inequality β_k ≥ h₁((h₁^{−1}β_k mod e₁) + (f₁−1)e₁), collapsing to the r3 form at f₁ = 1), so borderline [M]/[T] like (R1)–(R4); kept [M] for honesty. **Automaticity, exact:** automatic at r = 0 ONLY (dim = f₀ = d on nonnegative on-line data); NOT automatic at r ≥ 1 (two explicit r = 1 countermodels on file); every older "automatic at orders ≤ 1" phrasing in this document is superseded by this row [finding VC4-2's charge]. Enters Step 14 (CEN-W/CEN-J), hence Step 18's K3 census half (K3-b) AND Step 18b through seam (S1) [added at REVISION 4, finding VC4-5], AND Step 16/clause (UB) through Step 16's consumption of the census over any complete DVR [REVISION 3, finding B1]; carried by (ROOT-C)(H3); consumed by clauses (R)/(UB) only — NOT (SQ) [REVISION 4, finding VC4-4]. Unattained-vertex data have census 0 (the padding value), so the hypothesis prices attainment, not positivity. Falsifier state: K6 (class refuted, 0 = 0 exact) + K7 (value-vs-FULL dichotomy — countermodel refuted, first d ≥ 2 VALUE gate exact: census q^14(q²−1)² at p ∈ {2,3}). O-9 pass 4 in flight; the [M] classification is unchanged |
| **(UB-X)** — the clause-(UB) residue [NEW at REVISION 1, finding 7] | (a) the per-leaf O_δ re-base audit for the ℚ_p-stated leaves (the "per-leaf scope hygiene" of the D-3 collapse, declared at the GD dispatch but unwritten); (b) δ-stable position classes exhaust the realized ledger at every δ — **whose restriction to Step 18 K3-c's realized δ > 1 pools is the named fragment (K3-δ), consumed by clause (R) [REVISION 4, finding VC4-1]**; (c) full solve + type aggregation commute with unramified base change | D-3/O-8b (Step 16; the (K3-δ) fragment also Step 18) | until written, clause (UB) is proved ONLY at the Step-16 displayed scope; (ROOT-C) makes this explicit as hypothesis **(H4b)** (renamed from (H4) at the REVISION-2 split, finding V2-2 — since REVISION 4 the genuinely clause-(UB)-only part is (H4b) MINUS its (K3-δ) fragment: clause (R)'s attribution includes (K3-δ) until the δ-stable match display lands at the O-11/O-8b interface). N8 numerically supports the law it scopes |
| **D-12r** | TB-CAP's (τ-irr) completeness perimeter: the D4R.0-K(c) verdict-pin residual | [3t] VP owner (tree D-12r) | perimeter-conditional wherever TB-CAP is consumed (Steps 2 (T-6's declared TB-CAP conditionality), 3, 11, 12, and Step 19 — where T-6's leg serves the classifier-side counting tie inside the evaluation squeeze, at clause (R)'s conditionality; the REVISION-3 A6(ii) phrasing "the (SQ) bracket consumes T-6" is SUPERSEDED at REVISION 4, finding VC4-4 — the semantic (SQ) bracket is Step 1's, unconditional); displayed, not discharged |
| **(E-N)** | O-1thr Theorem 3(c)'s exhaustion caveat | O-1thr package | OPEN, scoped, touches CU-4 through Thm 3(c) (risk row R2 of the O3adj display); NOT consumed by the mandatory path elsewhere |

**(AGR) relocated [REVISION 1, finding 10]:** the drainage agreement seam
(= OL1-ii at general n: canonical termination + acceptance below a finite N(f)) is
ASSEMBLED from CU-2 + CU-4 + GMN Cor 4.19 — all on file — so under this ledger's own
definitions it is NOT [M]: no new mathematics is missing. It now lives in §3.2 as the
inherited-[V] row it is; general-n drainage stays conditional until those passes land
(n ≤ 3 unconditional, O4T Thm N3).

### 3.2 Verification-pass debt [V] — proofs on file, passes owed (named)

| item | what is owed | owner |
|---|---|---|
| **P(O-2a r5)** | fresh hostile pass on O-2a rev 5 (core thrice confirmed; V25 arc) | O-2a (Step 7) |
| **P(O-1thr r4)** | fresh hostile pass on O-1thr rev 4 (V24's criticals repaired; sloped/sheared pin stands) | O-1thr (Step 6) |
| **P(O5t r3)** | fresh hostile pass on O5triple rev 3 (V23 0-critical arc) | O5triple (Step 12) |
| **P(O-8b/M14)** [NEW row at REVISION 3, finding B2] | fresh hostile pass on M14's conditional O-8b proof (on file; the alphabet law at δ-stable position classes over (R1)–(R4)) — the one consumed PROVED-UNVERIFIED proof whose pending pass was named nowhere; it sits on the mandatory path of clause (R) (Step 18's K3-c), not just (UB) | O-8b/M14 (Steps 16, 18) |
| **O4T r4 + confirming pass** [synced at REVISIONS 1/3] | rev 3 LANDED (bb4326c); pass 3 (acceptance) RAN — SOUND-WITH-GAPS, ZERO criticals (ed413ae; harness re-run 2.53M classes, sharpness confirmed), two one-line gaps → r4 (the two one-liners) **LANDED at revision close** (3956500, cores byte-stable) + ONE confirming pass to the bar | O4T (Step 13) |
| **O-9 r3 + pass 3** [synced at REVISIONS 1/3, finding 4] | rev 2 (01c21e6) survived on its pass-1 repairs, but pass 2 (af2293e) was **UNSOUND**: the (ADM) display's class-vs-value attainment equivalence FALSE (r = 1 countermodel) → r3 with the VALUE-attained (ADM) reading **LANDED at revision close** (460ea59; automaticity rescoped, K6 falsifier 0 = 0); pass 3 owed on r3 | O-9 (Step 14) |
| **D-11 verification cycle (at r3)** [synced at REVISIONS 1/3] | pass 1 NOT ACCEPTED as billed (2587c70) → r2 (566b967) → pass 2: 2 criticals, both CONTAINED at **r3** (8a0786c: M1(a) rescoped, completed-node overclaim withdrawn — honestly LAYERED; M2.0 rewritten over countable addresses); pass 3 owed | D-11 (Steps 17/18b) |
| **O-11 verification cycle (at r3)** [synced at REVISIONS 1/3] | pass 1 NOT ACCEPTED AS STATED (a7ede72) → r2 (1bd8bd1, D-a/D-b/D-c declared + oracle-pin supplement) → pass 2 (V32): billing precision → **r3** (7aef1b9: tier 2 split into hypothesis-grade rows H-1..H-4; walk/cores byte-stable); pass 3 owed | O-11 (Step 18) |
| **CUC + CU-2t R2 re-pass** [synced at REVISION 3] | pass 1 **UNSOUND** (b9d1d70: the Θ^τ ν-blindness critical + 9 gaps; §6.1 audit sound) → **CU-2t R2 LANDED** (unit of record 567814d: Definition RC displayed, the critical + its root repaired, the (T-DEC)/(T-VERD) pricing honesty-corrected — residue +2 GD-4 rows, see the §3.3 row; disposition table CUC §10); hostile re-pass on the R2 record owed | CUC (Step 11) |
| **(AGR) inherited [V]** [relocated from §3.1 at REVISION 1, finding 10] | the drainage agreement seam, ASSEMBLED from CU-2 + CU-4 + GMN Cor 4.19 (all on file); its residue = exactly the pass debts of CU-2/CU-4 (this table) + the Cor 4.19 literature row (§4) — nothing else | O-4/O4T TR-OM (Step 13) |
| **Dfloor 3 minor gaps** | ID reduced-rep, ADD induction coprimality, TRANSFER sum-regularity — ride the next doc touch | Dfloor (Step 1) |
| **O-10 2 minor gaps** [added at REVISION 3 status sync] | the D-8 value-vs-law framing (collapses definitionally) + the box-count transport cite — found at the VERIFYING pass 2; **repaired at O-10 r2, landed at revision close** (3956500: the D-8 separation dropped as definitional with the existence range displayed; the (BOX) transport display + M07 §2.1 cite row; cores byte-stable). Per the wave-14 ledger: VERIFIED (leaf #6) STANDS, framing fixed; the r2 diff-confirmation rides the next harvest | O-10 (Step 15) |
| **B-layer verification rounds** [row added at REVISION 1, finding 3; B-4 added at REVISION 2, finding V2-4; **B-3 (doc level) added at REVISION 3, finding B4**] | B-1, B-2 (doc level), **B-3 (doc level)**, **B-4 (order-r layer)**, B-5, B-6, B-7 are PROVED-UNVERIFIED June documents (grades displayed at Step 2); the tree §4 protocol already schedules their verification-only rounds; B-3's core and B-2's counting core are VERIFIED-LEAN (B-3's doc level has the same status shape as B-2's — Lean-verified core + PROVED-UNVERIFIED June document — and is now listed like it); B-4's order-1 instance = B-3's VERIFIED-LEAN core, and its order-r content (`M6_lemma.md`) has as modern face O-9's OL-B, discharged to GD-3 — on the modern path the orders-≥ 2 content rides §3.1's (GR-B), so this row prices only the June-document verification rounds; B-8 SUPERSEDED, cited nowhere | B-layer (Steps 2, 3) |
| **K-12 faithfulness-audit record** | the Lean `undec`/`hExhaustP` vs mathematical-classifier audit (DELTA-1 §D1.5(g)); grade held pending | K-12/n = 2 anchor |
| **End-to-end passes on THIS document** [synced at REVISIONS 1/3] | passes 1–3 RAN, each COMPOSITION-GAPS → each repaired by its revision (§§7–9): VC1 (Codex) → REVISION 1; VC2 (Codex) → REVISION 2; VC3 (Fable, model-diverse) → REVISION 3 — VC3 confirmed the composition's MATHEMATICS (all findings attribution/ledger integrity). The criterion: ≥ 2 consecutive CLEAN end-to-end passes, ≥ 2 models, verifiers who saw none of the per-leaf rounds (tree §4 Root criterion); the consecutive-clean counter is at ZERO; next = VC4 (Codex) on this thrice-revised document | Phase C |

**GD23 row RETIRED [REVISION 1 status sync]:** the former "GD23 gap-9 light repairs"
row is DISCHARGED — rev 4 repaired all 9 gaps (f9878d1, cores byte-stable), the
gap-check ran clean, and GD23 was ADJUDICATED **VERIFIED (leaf #4)** at the 2026-08-02
harvest (c43b13b). No GD23 pass debt remains; its (GR-B) conditionality stays in §3.1.

**CU-1 and O-10 rows RETIRED [REVISION 3 status sync]:** the former "CU-1 r5" and
"O-10 pass 2" rows are DISCHARGED at the 2026-08-02-night harvest (ledger 7b28562) —
CU-1's r5 gap-check ran GAPS-CLOSED (0/0, commit 5329a4e) → **VERIFIED (leaf #5)**;
O-10's model-diverse pass 2 ran SOUND-WITH-GAPS with the mathematics airtight
(5296528) → **VERIFIED (leaf #6) at scope** (its two minor gaps ride as the doc-touch
row above). No CU-1/O-10 pass debt remains; CU-1's (GR-B)/pin conditionality and
O-10's K-LOC/(I-τ) interfaces stay where they are (§3.1/§3.3).

### 3.3 Transcription/audit debt [T] and named pins/flags

| item | content | owner |
|---|---|---|
| **GD-5 residue: the S-1 audit (incl. C.1.5)** | the one-page composition note + machine transcription audit (O-1thr machine ↔ O-2a stage interface F.0–F.2 at order 1) + the degree-g > 1 KEY1 generalization (same method). **Explicitly includes C.1.5** [REVISION 1, finding 5]: T-2's deferred graded-presentation obligation ("downsets are literal digit systems") — definitional at the mathematical machine (O-1thr §4 (S-1)); its transcription half is THIS audit | GD-5 (D2.6 step 2) / T-2 → Step 6 |
| **D-5 disposition** [row added at REVISION 1, finding 5] | the tree's D-5 (WELLPOSED) carrier/equality design = O-2a rev 5 §§1–2 (two carriers, Θ, consistency predicate, Lemma R) — PROVED CONTENT of that leaf, verification debt = P(O-2a r5); the wider semantic-invariance clause is carried by each consuming leaf's own displayed carrier section (Steps 3, 6, 10), consumed nowhere as a separate node | O-2a (Step 7) |
| **(O6) canonicalizations** [row added at REVISION 1, finding 5] | O3design §1: branch-letter keying + deep-marker pooling — DEFINITIONAL census-side bookkeeping, no proof content (CUC §3(c)); V16/V21 arc on the O3design record | O3design → CU-3 (Step 11) |
| **GD-4 / GD-6 engine-bookkeeping units** | emission/record discipline (W1–W5, (c0), AUX band; K-OB-E's GMN Def-3.9 arithmetic is the one semantic clause) and run-decomposition conformance; proof-by-construction routes on record; CU-2t's (T-DEC)/(T-VERD) rows — RE-BILLED at the CU-2t R2 (567814d, CUC F4; folded here per the wave-14 charge) as **two genuinely NEW unproved mandatory-path GD-4 obligations** (in no printed clause list before CUC §9.4 displayed them; no new open family, but the residue GREW by these two rows — rev 1's "displayed GD-4 instances" wording understated them); GD-4's owner brief absorbs the §9.4 scope note at its next revision; **enters Step 18 through D-15's (M6b)(iii)/(ii−) clauses** (O-11 K4-CYL — declared row D-a at O-11 r2) | GD-4/GD-6 owners |
| **GD-7 flags: (GMN-COH)/(R-0)/(R-1)/(R-2)/(R-3)** | O5triple's five citation-grade flags (sprouted-type dissection, flow coherence, order-0 anchor, ADEQ read-back, representative lookup) — one GMN §2.1/§3/§4.1 reading session covers them; NOT covered by the executed LITUNIT | GD-7/literature unit (Step 12) |
| **GD-8 order ≥ 2** | the exact-key polygon seam beyond order 1 (order-1 proved, falsifier-covered); expected verbatim over GD-2's frame tie | GD-8 |
| **(KP)/(KPirr) beyond order 1 + properness proviso** | GD-1's representative-admissibility clauses; properness a genuine side condition only at e·g = 1 refinement reads (FGMN Lemma-5.3 discharge displayed) | GD-1 |
| **Declared pins (P-ROOT)/(P-KEY)/(FR≡)** | CU-1's three declared pins replacing silent cross-brief glue; (FR≡) has refutable order-2 content = the gate's coherent-convention finding | CU-1 (Step 10) |
| **Sloped/sheared convention pin** | O-1thr's window-height convention (the depth-2 falsifier forced it; 41,720/0 vs 7,472 violations unsheared) | O-1thr (Step 6) |
| **(I-τ) + K-LOC interface** | the adapted-cell → engine-stratum presentation for O-10's Theorem 2 (K-LOC = M07 OL-3: continuation reads of branch j = OM reads of f_j up to cell-constant normalization) | GD families / O-10 consumers (Steps 15, 18) |
| **(S1)/(S2) seams of D-11 M2** | (S1) = GD-3-FULL/O-9 hand-off ← Step 14 (+ (GR-B)); (S2) = the O-11 composition datum ← Step 18. Since REVISION 1 (finding 2) the step order 17 ≺ 18 ≺ 18b makes both seams STRUCTURALLY earlier — the acyclicity is in the walk itself, and the seams discharge when Steps 14/18's passes land. D-11 r2 (566b967) declares a THIRD seam **(S3)** = the projective assembly weight's MASS reading, owner annex A-1 — POSITIONED at REVISION 2 (finding V2-1): (S3) conditions ONLY the projective reading of M2's conclusion (the r2's own scoping), which NO §2 step consumes — Step 18b consumes M2 at monic scope, and the projective normalization is annex by standing directive; (S3) is therefore an ANNEX A-1 obligation, not mandatory-path residue, and appears in no (ROOT-C) hypothesis | D-11 (Step 18b, non-consuming) / annex A-1 |
| **OL-O12-1 contingent-escape flag** [row added at REVISION 3, finding A7] | Step 5's (B-INST) escape: fires ONLY if a future pack departs from 𝔅_n's three on-record kernel organizations — currently UNFIRED and consumed by NOTHING; homed here per the §7 closing standard (every named pin/flag has exactly one ledger home). If it ever fires, the O-12 pole-freeness theorems need re-derivation at the new organization | O-12 (Step 5) |
| **OL-O12-2 data pass** | the finite transcription/correspondence pass identifying the complete degree-3 table as an (O3) member of 𝔅₃ (math half closed at D-11) | O-12/D-11 |
| **T-U §U.SQ.6 correspondence audit** [row added at REVISION 3, finding A8] | Step 19 consumes THEOREM U conditional on its displayed §U.SQ.6 kernel ledger, discharged by the claim that the ledger's items coincide with the Steps 1–18b roster + the recorded evictions/re-routings (e.g. the R-QNT kernels struck at DELTA-1 §D1.4) + the annex items; the ROW-BY-ROW correspondence is ASSERTED, not displayed — a fresh reader of this document cannot check that no §U.SQ.6 item falls outside the steps. The display table (per-item pointer §U.SQ.6 → step/eviction/annex) is owed here | T-U (Step 19) / Phase C |
| **BASE-1(f) fence** | Dfloor's classifier-side n = 1 clause, fenced to the classifier steps (served by Steps 6–13's package) | Dfloor/CU |
| **LC-COH** | the displayed open note from the O-3 clause-3 re-key — CONSUMED BY NOTHING (kept for honesty) | tree D2.1 line 1 |
| **(REP-IRR)** | the unpinned literature pull behind the QUARANTINED Corollary CU-2t-deep (GD-8 corner) — consumed by nothing mandatory; flagged to the literature unit | CU-2t/literature unit |
| **W3 carrier note** | the τ-irr seam object is a PAIR, not an 𝔈-concatenation (CU-2t display; convergent with CU-1's split) | CU-2t |
| **LIT-1 printed-TAMS pagination** | the standing GMN confirmation duty (LITERATURE-CONDITIONAL until confirmed); one session with the printed TAMS covers it + the GD-7 flags | literature unit |
| **LIT-3 numbers + Mathlib probe** | Neukirch II §4 Prop 4.6 / Serre LF I §6 numbers to confirm at declaration; probe `HenselianLocalRing` first | literature unit (Step 12) |
| **LIT-8 per-use-site transcriptions** | LIT-8a..8e split (DELTA-1 §D1.5(d)); exact numbering owed at each declaration site (O4T's inventory did this for its own sites; Dfloor displays statements) | per consumer |
| **O-11 → D-11 widened-charge items (v)–(vii)** [row added at unit TREE-GAPS, audit gap G-4 — REVISION 1's §7 note "(5) ... noted pending acceptance" promoted to an operative row] | O-11 r2/r3's restated D-11 entry WIDENED the WAVE-8 charge: (v) the pack's carried laws rsh_interp/r_bdd/wsh_ok; (vi) the DVR scope-hygiene audit of K3-c; **(vii) general-n H.6 in-fence conformance of the built tables** — the surviving live condition of the tree T-5 row's "six H.6 fences gate [1v]-FULL" (Step 18's fence display; full adjudication + fence-by-fence mapping: tree DELTA 4 §D4.2): the six fences stay the H-DOMAINS perimeter's open kernels (owners/refuters unchanged, off the mandatory path); what Step 18's K3-a consumes is ONLY this conformance, proved nowhere at general n (V-n3/H-n3 are sealed n = 3 evidence). Acceptance owed by the D-11 owner; borderline [T]/[M] — kept [T] as an instance-pin construction/audit duty riding D-11's PENDING grade; ESCALATES to §3.1 [M] on clause (R)'s chain if the D-11 owner rejects the charge or a built pack exits the fenced perimeter. Whether (vii) should be promoted to hypothesis grade like D-11's clause 4 (= (H5)/(PACK), REVISION 4) is flagged to the next VC pass | D-11 (Steps 17/18) / O-11 r3 §0 |
| **O-14a/b/c engine-residue dispositions** [row added at unit TREE-GAPS, audit gaps G-1/G-2/G-3] | tree D-10's O-14 split, homed: **O-14a** guarded vertex-transport law — CLOSED at the e′ = 1 sub-perimeter, Lean twin `lean/LeanUrat/HC2/HK11a_vertexTransport.lean` (σV-vertex law, Lean-core); unguarded form stays REFUTED (HK52_stretchGate); ≥ 2 disposition = sign-off item 28 (the PARKED row above); consumed by NO §2 step (engine-internal — the Lean bridge's V9/HK cone; GD-2's clause-(c) HK52 trap is the ≥ 2 countermodel, not a consumption). **O-14b** cl19 repaired carrier ladder (post-K-7: the O1–O3 semantic ladder at a real carrier pack) — OPEN; K-7's "repaired carrier form" pointer lands HERE; sole consumer = the Lean-bridge slot wiring (queue item 22, `REMAINING_CENSUS_2026-08-01.md`; theoremU's slot bare-Prop, SAFE), PARKED by the 2026-07-31 math-first directive (fe3cda5). **O-14c** hStateNe — OPEN, expected derivable; = `BridgePre.hStateNe`, a named ratified Lean-bridge premise (BRIDGE_ADJUDICATIONS Q3); standing disposition = the IB-B2 derivation attempt (row drops if it closes). None of the three is consumed by any §2 step; none appears in any (ROOT-C) hypothesis (display sweep at unit TREE-GAPS, incl. the REVISION-4 (H5)) | Lean side, post-math (tree DELTA 4 §§D4.3/D4.4) |
| **Item-27/28 Lean statement repairs + O-14d instance population** | PARKED engineering (Lean statement fences; the wave-D carrier population) — outside the math criterion by DELTA-1 §D-10 | Lean side, post-math |

**What is NOT on the ledger (evicted from the mandatory path, recorded):** O-2b/OB1
(trace correspondence), OB2/CU-6 (σ-invariance under ∼_OM — the DELTA-3 audit: D-11
needs per-box lift uniformity instead), LIT-5/BNS entirely (zero root-side touch-points),
K-OB-C (Okutsu proximity), **K-OB-D (certificate-firing at O-5's threshold — evicted by
containment: sole consumer O-7; named here at unit TREE-GAPS, audit A-3 — the last IFK
REV-1 obligation without an explicit disposition line)**, D-16 (δ-tier execution
transport), O-6/O-7/O-8a (track count/weight charge/linear rates), **and `cl3_tails`
(X2-TAILS measure/cone tail estimate — the tree O-8 row's SEPARATE open estimate, owner
§H-DOMAINS family; its OWN eviction row at unit TREE-GAPS, audit G-5: quantitative-rate
content of the X.2 pricing family, consumed by nothing count-native — the root's
undecided-mass control is drainage (Step 13), never tail rates; tree DELTA 4 §D4.5)** —
ALL route R-QNT, needed only if explicit rates are
elected. htameFE/palindromy + the projective bridge are ANNEX (A-1/A-2).

**Closed/refuted tree ids — content homes (tree-§4 criterion-4 display; added at unit
TREE-GAPS, audit A-1/A-4/A-5).** T-11/JOINT-D1 → Step 2 inside T-1's perimeter
(D1-marginal machine-checked, `OM/DevBijection.lean`) · K-1 ksub / K-2 w17ii / K-15 →
CLOSED Lean-interface rows, nothing left for the composition to consume · K-3 →
refuted (caterpillar countermodel cited at Step 3); repaired math = O-6, route R-QNT ·
K-5 → refuted; the per-site true statement = O-1 (Step 6) · K-7 cl19_rep → refuted;
repaired carrier form = O-14b (the §3.3 O-14 row above) · K-8 → adapted-cell math =
O-10 (Step 15) · K-9 cl6 → level 1 at Step 14 (M08 Thm 2); order ≥ 2 = O-9 · K-10
cl15_align → Steps 7/8 + the §4 GMN Thm 4.18 pin · K-14 duties: (I0)/(I1)/(I3-rc) →
Step 10 + the D2.3 consumer walk; **(I2) level coherence → definitional at the
statement layer against T-3 §D4-R's D4R.4/L12 stabilization level (N(P̂) = max
per-prefix resolution level, finite by L8; M18 fable §6.2's displayed warrant) — its
instance-build face rides the O-14d/D-11 population; not a missing consumer-walk
edge (audit A-4)**.

---

## 4. LITERATURE ROSTER (the goal's conditionality class)

Every external citation the assembled proof consumes, with its pin status. Discipline:
tree §4 rule 5 (verbatim published-text transcription + faithfulness entry + guardian
audit + sign-off before any axiom-grade use); the LITUNIT
(`lean/notes/openmath/LITUNIT_2026-08-01.md`) resolved every GD23 flag MATCH with
verbatim quotes at named extraction lines.

1. **[GMN] Guàrdia–Montes–Nart**, *Newton polygons of higher order in algebraic number
   theory*, Trans. AMS 364 (2012) 361–416 (= arXiv:0807.2620v2). THE machinery import.
   Pinned loci (via `docs/GMN_citations.md` + LITUNIT): Lemma 2.2(2); Prop 2.7(1)(3)(4);
   Lemma 2.17(2)(3); Def 1.8; Thm 1.15/1.19/Cor 1.20; Thm 2.11 + Defs 2.19–2.21;
   Thm 3.1/3.7, Cor 3.3/3.8, Defs 3.9/3.10, eq. (37); Lemma 3.11(3); Thm 4.18 (theorem
   of the index — declared, guardian-audited Lean axiom, read-set-restricted) +
   Cor 4.19 (termination); Defs 4.11/4.12/4.15. **LIT-4/(OM-SAT) rides this entry by
   id [added at unit TREE-GAPS, audit A-2]:** a realized OM branch with residual
   multiplicity 1 at its last read certifies an irreducible factor with e = e₁⋯e_r,
   f = f₀⋯f_r (Cor 3.8 + Def 3.9; order-1 instance Cor 1.20 — the pins Steps 11/12
   already consume); audited scope **"K = ℚ_p exactly"**, consumed only through the
   dictionary node O-2; its K_δ (δ > 1) re-scope duty is exactly (UB-X)(a) content
   (the per-leaf O_δ re-base audit, §3.1) — named here rather than ridden
   generically. Status: LITERATURE-CONDITIONAL
   (printed-TAMS pagination confirmation owed — §3.3). Consumed by Steps 7, 8, 11
   (CU-2t consumes Cor 1.20/3.8 directly — added at REVISION 3, finding A6(i)), 12,
   13, 14, and 15 (K-FACT = Thms 1.15/1.19 + 3.1/3.7 — Step 15's pinned perimeter,
   all four loci above) [Step 15 added at REVISION 2, finding V2-7].
2. **[ML] MacLane**, *A construction for absolute values in polynomial rings*, Trans.
   AMS 40 (1936) 363–395. Pinned (LITUNIT, re-typeset caveat displayed): Thm 4.2 (the
   (V1) multiplicativity), Def 4.1, Thm 10.2, Lemma 10.1, Lemmas 11.1–11.2, Thm 12.1,
   Cor 12.2 (commensurable hypothesis automatic here). Consumed by Steps 6, 8, and 9
   (Step 9's loci: Def 4.1 + Thm 4.2 — the (V1) frame-semantics pin, LITUNIT §4
   verdict MATCH; consumed as the intended semantics of T-1/T-2's frame vocabulary,
   no further MacLane theorem — Step 9 added at REVISION 2, finding V2-7) (and
   (GR-B)'s pinned targets).
3. **[FGMN] Fernández–Guàrdia–Montes–Nart**, *Residual ideals of MacLane valuations*,
   J. Algebra 427 (2015) 30–75 (= arXiv:1305.0775). Pinned: Thm 4.2 (BOTH printed
   pairings; exact match verified clause-for-clause at GD23 r3), Cor 4.4, Thm 4.8,
   Cor 4.9, Cor 5.6, Thm 5.8, Cor 5.12, Prop 5.14/Cor 5.15, Lemma 5.3 (properness).
   Consumed by Step 8 and (GR-B)'s target statements.
4. **[Serre LF] Serre**, *Corps Locaux / Local Fields* (GTM 67). Ch. II §2 Prop 3
   (integral closure is a DVR — the declared axiom `AX_integralClosure_dvr`, guardian
   audit PASSED, V3: FAITHFUL/EXACT); Ch. II §2–§3 (unique valuation extension;
   Σe_if_i = [L:K] defectlessness); Ch. III §6 Prop 13 (wild different bound, June
   L5fix). Consumed by Steps 1, 12, 13 (Facts EXT/EF) and B-6.
5. **[Neukirch] Neukirch**, *Algebraic Number Theory* (Grundlehren 322). Thm II.4.8
   (valuation extension; the M16-precedent high-confidence pin); II §4 Prop 4.6 =
   LIT-3 coprime-Hensel (LITERATURE-CANDIDATE: numbers to confirm, Mathlib probe owed);
   II §6 region (fundamental identity). Consumed by Steps 12, 13.
6. **[Lang] Lang**, *Algebra* (rev. 3rd ed., GTM 211), Ch. IV §8
   (resultant/discriminant; number flagged for page verification) — O4T Fact D.
   **[Cohen] Cohen**, *A Course in Computational Algebraic Number Theory* (GTM 138)
   §3.3 (coefficient-side resultant — also what the harnesses compute). Step 13.
   **O4T import inventory — COMPLETE at rev 3 [REVISION 1, finding 8]:** the eight
   named Facts beyond NP/SF/HEN are EXT, EF, D, GRD, UCT, HRG (rev 2, sources as
   displayed in the O4T record) **+ SEP (char-0 separability of irreducibles) + DES
   (Galois descent/fixed field)** — the pass-2 "Galois descent + one more" pair, both
   added at rev 3 (commit bb4326c) as IN-LINE-PROVED imports with consumption-site
   cite tags (standard field theory; no new external citation is consumed — the
   proofs are in the leaf). Six-vs-eight reconciled: EF and GRD each bundle two of
   V30's items.
7. **[LIT-8 split, per DELTA-1 §D1.5(d)]** LIT-8a Krasner + the 2v+1 polish constant
   (inside VERIFIED M05 Lemma D); LIT-8b Newton–Hensel; LIT-8c Vandermonde/resultant
   identities (Bourbaki *Algèbre* IV §6 / Lang); LIT-8d Igusa §7.4 change of variables;
   LIT-8e Gauss/Möbius counts. Each LITERATURE-CANDIDATE, transcribed at its use site.
   Consumed by Steps 1, 13, 15 and the B-layer.
8. **Standard graduate measure theory with displayed statements** (Dfloor's audit:
   Folland *Real Analysis* Thm 1.14 (premeasure extension), Thm 2.37 (product/Tonelli),
   Tychonoff/Carathéodory/π–λ). Step 1. **[Serre CA] Serre**, *A Course in Arithmetic*
   (the n = 2 split criterion used in Dfloor's unconditional instance).
9. **In-project Lean-audited axiom set** (not literature but axiom-grade trust,
   `docs/AXIOM_FAITHFULNESS.md`): the GMN index theorem (item 1's Thm 4.18 declaration)
   and — measure route ONLY, NOT consumed by this count-native assembly — the
   Denef–Igusa cell recursion (`PadicMeasure.AX_cellRecursion`).

**Explicitly NOT consumed:** [BNS] Bauch–Nart–Stainsby LMS JCM 16 (2013) — route
R-QNT only (DELTA-3: zero root-side touch-points); [DCD] Del Corso–Dvornicich — annex
A-2 only (the 2026-07-21 retirement stands); the companion 2212.00294 (excluded by
standing goal directive).

---

## 5. NUMERICS CORROBORATION INDEX (flags, never substitutes — tree §0)

Standing matrix (tree §5) + the Phase-B falsifiers, keyed to §2's steps. Every leaf
with a runnable falsifier RAN it before acceptance (countermodel-first discipline).

| suite / falsifier | what it corroborates (step) | result |
|---|---|---|
| n = 2 Lean capstone + `verification/census_n2_uniform.py` | THE ROOT at n = 2, machine-checked + external census (anchor) | exact at p = 2, 3 |
| RESUM-n3 | the assembled pipeline's n = 3 densities (Steps 2, 18) | 65/65 exact, PARI 0 mismatches |
| N1 exhaust / N2 density-tie | bracket + drainage; the root numerically to n ≤ 5 incl. (5,5) (Steps 13, 19) | CONFIRMED (max ratio 0.858 < 1; sandwich ~1e-5) |
| `dfloor_checks.py` | Step 1 (incl. the T-F n = 3 interpolation certificate) | ALL PASS |
| O-13 enumerator reproduction | Step 3 (verifier re-implemented from text alone) | \|S_n\| = 1, 15, 53, 197, 509, 1460 exact |
| N6-regp + ext2000 | Steps 4, 5, 17 ((REG-p) emptiness, margins) | 25/25 gates; 303/303 primes < 2000, margin sharp 6/7 |
| O-1thr depth-2 falsifier (T-E/T-F harnesses) | Step 6's sheared convention | 41,720 instances 0 violations (7,472 violations of the UNsheared reading — the pin is load-bearing) |
| GD23 (L3+) harness | Step 8's order-1 exact-key seam | 871 forced samples, 0 findings |
| U6 / IFK-U6-FIRST + the depth-3 falsifier (CU-1's gate) | Steps 10–11 (no-phantom, counting tie, equal fibers) | 174/174 length-2 strata T = T̂, 369 chains, 0 phantoms, PARI 1600/1600; depth-3 gate SURVIVED pre-rev-1 |
| `O4T_transfer_check.py` | Step 13 (n ≤ 3 ceiling sharpness, envelope) | 2,534,851 exhaustive classes, 5 configs incl. wild, ALL PASS, max ceiling slack 0 |
| `o9_order2_census_check.py` (M08-T6) | Step 14 (order-2 census polynomiality) | 8,220,994 boxes, 1,128,288 order-2 instances, K1–K4+T2 0 violations, 18 cross-p cells, ε = 0 |
| `o10_kcount_harness.py` | Step 15 (K-COUNT fiber law; sealed predictions) | 68 PASS / 0 FAIL |
| N8 eq2 | Step 16 (the alphabet law) | 199,723 alphabets / 17 fields, 0 violations |
| `o11_seriestie_check.py` | Step 18 (incl. Finding F1's test at the assembled-pack proxy) | 38/38 billed; the O-11 pass-1 record corrects the live count to 37/37 (one test = discriminant proxy) — flag stands either way; n = 2 true triple identical in ℚ(q) |
| N3/N4/N5/N7 + the 22 sealed T-layer gates (D4-n3 404M boxes, SIB 32/32, T-n3, M-n3-V2, H-n3 151/151, V-n3 178/178, STATE-probe-2, …) | the §2.2 layer (Step 2) | ALL PASSING |

Matrix synthesis (adjudications ledger): no Fable-vs-Codex-vs-numerics conflict
anywhere; every refutation triangulated; every surviving conjecture numerically
supported. Root criterion 3 (tree §4): this matrix re-runs green at acceptance time.

---

## 6. Change discipline and next actions

This document is Phase C's spine. Update rules: it re-states the tree + DELTAs and the
wave-10 ledger; where they move (DELTA 4 at the next fold), a dated appendix here
records the delta — the body above stays byte-stable per the tree's own discipline.
Acceptance path (tree §4 Root): (1) empty §3.1 and §3.2 into VERIFIED (the [M] rows
via the GD campaign's order-≥ 2 arc; the [V] rows via the named passes); (2) ≥ 2
consecutive clean END-TO-END passes on this document by fresh verifiers, ≥ 2 models;
(3) the §5 matrix re-runs green; (4) the completeness audit: every tree node id appears
here or in the recorded eviction list (§3.3's final paragraph + the tree's DELTAs).

Immediate dispatch order (updated at REVISION 1; the O-9 E′ and O4T N3-BRACKET
repairs have LANDED): the D-11 and O-11 r2s (+ their re-passes); CU-1 r5 (in flight);
the O4T full clean pass; the CUC/CU-2t pass; the three registry passes
P(O-2a r5)/P(O-1thr r4)/P(O5t r3); O-10's pass 2; the (UB-X)/(R1)–(R4) write-up; then
the GD order-≥ 2 campaign for (GR-B)/(FRESH) — the last genuine mathematics between
this assembly and the theorem. [Superseded event: the pass-2 slot RAN as VC2 and
returned COMPOSITION-GAPS — dispositioned at §8 (REVISION 2); the next end-to-end
pass (VC3, fresh verifier) runs on THIS twice-revised document, and the ≥ 2
consecutive-clean counter is still at zero.] [Updated at REVISION 3: VC3 RAN —
COMPOSITION-GAPS, all attribution/ledger integrity, the mathematics CONFIRMED —
dispositioned at §9. Dispatch now: **VC4 (Codex) on this thrice-revised document**
toward the two-consecutive-clean bar; the wave-14 repairs LANDED at revision close
(460ea59/567814d/3956500: O-9 r3, CU-2t R2, O4T r4 + O-10 r2) — their confirming
passes (O-9 pass 3, the CU-2t R2 re-pass, O4T's acceptance pass) are the in-flight
debts, with the D-11/O-11 pass 3s; owed: P(O-2a r5)/P(O-1thr r4)/P(O5t r3),
P(O-8b/M14) (§3.2, new), the (UB-X)/(R1)–(R4) write-up; then the GD order-≥ 2
campaign for (GR-B)/(FRESH).]

— ROOT ASSEMBLY complete, 2026-08-02. Composed at HEAD d730669 + the recorded
in-flight events (O4T pass 2, untracked). Every §2 grade traces to a named commit or
pass record; nothing above upgrades any leaf's status. REVISION 1 (§7) applied after
VC1 at the 2026-08-02 harvest state (c43b13b). REVISION 2 (§8) applied after VC2
(bfa462f dispatch record; no status syncs — VC2 was a composition pass on this
document alone). REVISION 3 (§9) applied after VC3 at the 2026-08-02-night harvest
state (7b28562: VERIFIED = 6).

---

## 7. REVISION 1 (2026-08-02, unit ROOT-R2) — disposition of VC1, the Phase C end-to-end pass 1

**The pass.** VC1 = the first end-to-end verification of this document (Codex, fresh
context, dependency-graph charge: "a named input counts only if an earlier step
supplies it, a ledger row classifies it, or the literature roster carries it";
`lean/notes/openmath/VC1_root.jsonl`). Verdict: **COMPOSITION-GAPS (findings 1–8
blockers, 9–11 advisories)** — "the assembly is not composition-sound as written...
forward edges, a genuine D-11/O-11 cycle, several unbound inputs, and an incomplete
literature inventory." Every finding was accepted and repaired IN PLACE (the body
above is edited, against the §6 byte-stability default, per the standing repair
directive); this section is the audit trail. The step-by-step walk's FAIL/GAP verdicts
(Steps 1–3, 6, 7, 9, 11, 14, 16–19) are subsumed by the findings below.

**Disposition table.**

| # | class | finding (compressed) | disposition | where |
|---|---|---|---|---|
| 1 | BLOCKER | Step 1 silently consumes T-6 (ns-null), supplied only at Step 2 | ACCEPTED; the edge is REMOVED, not waived: the dependency is re-pointed to Dfloor's own Appendix A (self-contained ns-null via LIT-8c, inside the VERIFIED leaf-#3 perimeter — the fact the leaf actually proves); T-6's (ns-null) is declared NOT consumed | Step 1 |
| 2 | BLOCKER | D-11 M2 consumes (S2) = O-11's datum while O-11 consumes D-11's pack side — a genuine cycle | ACCEPTED; STRATIFIED exactly as the verifier proposed: D-11 {M1, M1′, M3} = Step 17 ≺ O-11 = Step 18 ≺ D-11 M2 = NEW Step 18b; both results displayed; no mutual dependency remains | Steps 17/18/18b, audit trail |
| 3 | BLOCKER | B-1..B-7 outside the document's dependency universe | ACCEPTED; grades inlined at Step 2 from tree §2.1 (B-2/B-3 cores VERIFIED-LEAN; B-1/B-2doc/B-4/B-5/B-6/B-7 PROVED-UNVERIFIED; B-8 SUPERSEDED, uncited); §3.2 B-layer row added | Step 2, Step 3, §3.2 |
| 4 | BLOCKER | O-9's refuted census exponent misfiled as [V] ("a proof is on file" was false) | ACCEPTED for the composed state; since then the rev-2 repair LANDED (01c21e6: E′ strict left tail, countermodel now predicted exactly; JUNCTION-PIN withdrawn → (FRESH)(c)) — the row is [V] again, re-pass owed | Step 14, §3.1 (FRESH), §3.2 |
| 5 | BLOCKER | unbound inputs: C.1.5 (Step 6), D-5 (Step 7), (O6) (Step 11); Steps 9/16 lack Consumes lists | ACCEPTED; all suppliers displayed: C.1.5 = T-2's deferred obligation → the S-1 audit row; D-5's carrier design = O-2a rev 5 §§1–2 (proved content, debt = P(O-2a r5)); (O6) = O3design §1 definitional canonicalizations; Consumes lists ADDED to Steps 9 and 16; the registry re-worded as metadata | Steps 6/7/9/11/16, §3.3 |
| 6 | BLOCKER | displayed theorem unconditional; steps prove a conditional implication | ACCEPTED; (ROOT) re-badged as THE TARGET; **(ROOT-C)** — hypotheses (H1)–(H4) = exactly the §3.1 [M] rows — displayed as THE theorem the composition proves, with the [V]/[T] rows displayed as audit debts on the implication's proof, not statement hypotheses; Step 19 closes at (ROOT-C) | §1, Step 19 |
| 7 | BLOCKER | universal (UB) stronger than the Step-16 support (δ-stable classes, conditional (R1)–(R4)) | ACCEPTED; the exhaustion debt DISPLAYED as new §3.1 row **(UB-X)** (per-leaf O_δ audit; class exhaustion; aggregation/base-change commutation); Step 16 restated at honest scope; (ROOT-C)(H4) carries it | §1, Step 16, §3.1 |
| 8 | BLOCKER | literature roster incomplete: O4T's "Galois descent + one more"; K-FACT's GMN source unpinned | ACCEPTED; the missing pair NOW EXISTS — O4T rev 3 (bb4326c) added Facts **SEP** + **DES** as in-line-proved imports (inventory complete at eight named Facts, six-vs-eight reconciled); **K-FACT = GMN Thms 1.15/1.19 + 3.1/3.7** (`docs/GMN_citations.md`), all four loci already §4-pinned | Step 13, Step 15, §4 item 6 |
| 9 | ADVISORY | general-n 𝔅_n instance correspondence insufficiently explicit | ACCEPTED; **(B-INST)** displayed: the consumed pack is BY CONSTRUCTION the 𝔅_n member (three on-record organizations; OL-O12-1 the contingent escape); no theorem claims more; degree-3 realized-table identification = the OL-O12-2 data pass | Step 5 |
| 10 | ADVISORY | (AGR) mislocated in [M] | ACCEPTED; relocated to §3.2 as an inherited-[V] row (assembled from CU-2 + CU-4 + Cor 4.19, all on file) with a §3.1 tombstone note | §3.1, §3.2 |
| 11 | ADVISORY | Step 19 conflates O-11 (series = R_τ) with D-11 M2 (density = series) | ACCEPTED; both results displayed as labeled statements; Step 19's attribution now names both tranches and states neither alone delivers α = R_τ | Steps 18/18b/19 |

**Status syncs applied with the repairs** (all at the 2026-08-02 harvest, ledger
c43b13b): **GD23 = VERIFIED, leaf #4** (rev 4 gap repairs f9878d1 + gaps-closed check;
the premature d730669 adjudication superseded); **O4T = repaired at rev 3, awaiting
one full clean pass**; **CU-1 = rev 5 in flight** (rev 4 landed 8ab8ca6; gap-check
GAPS-REMAIN; NOT VERIFIED — the headline's leaf count corrected 5 → 4); **O-9 =
repaired at rev 2** (01c21e6), re-pass owed; **D-11/O-11 pass 1s = NOT ACCEPTED**
(2587c70 / a7ede72), r2s owed. Nothing in this revision upgrades any leaf; it corrects
this document's own composition and bookkeeping.

**What VC1 pass 2 should check first:** the three structural repairs (Step 1's
Appendix-A re-point; the 17 ≺ 18 ≺ 18b stratification; (ROOT-C) vs the Step-19 close),
then the §3 completeness standard ("every named pin/flag has exactly one ledger
home"), which findings 3/5 showed is the failure-prone invariant.

**Concurrent in-flight events recorded at REVISION 1 close** (landed by parallel
units while this revision was being written; statuses in the body are AS OF the
c43b13b harvest, with bracketed in-flight notes at the affected rows): **D-11 r2**
(566b967 — the pass-1 critical contained as specified; (S3) declared) and **O-11 r2**
(1bd8bd1 — D-a/D-b/D-c declared; oracle-pin supplement 10/10) landed, pass 2s
launched; **CU-1 r5** landed (6299a4a — the GAPS-REMAIN item repaired); the
PROJECT_STATE refresh landed (3896eb0). O-11 r2's §9 owed ROOT touches are EXECUTED
here: (1) Step 18 names D-a/D-b/D-c with engine-proxy language; (2) the §3.3
GD-4/GD-6 row gains its Step-18 entry line; (3) the §3.1 (R1)–(R4) row gains "hence
Step 18"; (4) the (I-τ)+K-LOC row already listed Step 18; (5) D-11's widened charge
items (v)–(vii) noted pending acceptance; (6) the 37/37 falsifier-count correction
displayed (§5 + Step 18). Bookkeeping note: commit 4e03512's staging sweep captured
an intermediate state of THIS revision alongside the O-11/D-11 fold; this commit is
the revision's unit of record.

— REVISION 1 complete. The body above is the operative composition; VC1 pass 2 runs
on this document as a whole.

---

## 8. REVISION 2 (2026-08-02+, unit ROOT) — disposition of VC2, the Phase C end-to-end pass 2

**The pass.** VC2 = the second end-to-end verification (Codex, fresh context, same
dependency-graph charge as VC1, run on the REVISION-1 document;
`lean/notes/openmath/VC2_root.jsonl`). Verdict: **COMPOSITION-GAPS** — 5 blockers +
2 advisories, numbered V2-1..V2-7 in report order. VC2 also CONFIRMED the three
REVISION-1 structural repairs: "the two theorem statements are honestly
distinguished", "the original D-11/O-11 cycle and Step-1 forward edge are repaired"
(V2-3 is the explicit ADVISORY confirming the Appendix-A re-point compositionally
valid). Every finding is dispositioned below and repaired in place; this section is
the audit trail. Repairs are at named sites only; the §2 walk, both theorem
statements' mathematical content, and all leaf grades are otherwise byte-stable —
nothing here upgrades any leaf.

**Headline finding (V2-6, the one REAL mathematical bug in this document):** the §1
clause-(R) display quantified the self-loop resummation 1/(1 − q^{−(e(e+1)/2−1)})
over unrestricted e — at e = 1 the denominator is 1 − q⁰ = 0. Adjudication against
the solve structure (O-12 rev 4 §§2.2–2.4 + Thm 1 + Cor D): **e ≥ 2 is FORCED at
every self-loop** — inter-block bookings descend strictly (Lemma L4: m, μ < e), so
self-loops are within-block only, and block 1 has NO loop (K_1 = (0), Φ_1 = 1,
E(1) = {1}; Theorem 1 is stated "for e ∈ {2, …, n}"; multiplicity-1 atoms terminate
as simple Hensel factors). The e = 1 corner is VACUOUS; the leaf was never wrong —
the ROOT display was. Proof now DISPLAYED as **(SL≥2)** at Step 5; §1 quantified.

**Disposition table.**

| # | class | finding (compressed) | disposition | where |
|---|---|---|---|---|
| V2-1 | BLOCKER | Step 18b names only (S1)/(S2)/(r1) while D-11 r2 declares seam (S3), sent to annex A-1 — an unpositioned annex edge; the acyclic composition not closed | ACCEPTED as a display gap; RESOLVED by the r2's own scoping, now displayed: (S3) = the projective assembly weight's MASS reading conditions ONLY the projective reading of M2's conclusion ("M2 as stated (monic ensemble) does not consume it" — D-11 r2 §3 + Theorem M2's bracket); Step 18b consumes M2 at MONIC scope = clause (0)'s ensemble, so NO §2 step consumes (S3); it is an annex A-1 obligation, in no (ROOT-C) hypothesis. Step 18b's scope display added; §3.3 row repositioned. The dependency graph closes without the edge | Step 18b, §3.3 |
| V2-2 | BLOCKER | (H4) declared "for clause (UB) only", but Step 18's K3-c consumes O-8b/(R1)–(R4) (declared row D-c), so clause (R) depends on part of H4; and the "Without (H4)" sentence asserted the (R1)–(R4)-conditional alphabet law hypothesis-free | ACCEPTED — a genuine leakage; (H4) SPLIT: **(H4a)** = (R1)–(R4), consumed by clause (R) (Step 18 K3-c, base-changed β-legs) AND clause (UB) (Step 16); **(H4b)** = (UB-X), clause-(UB)-only. Per-clause hypothesis attribution displayed in (ROOT-C); the "Without (H4)" sentence corrected (alphabet law now stated under (H4a)); Step 16/18/19 + §3.1 rows synced | §1, Steps 16/18/19, §3.1 |
| V2-3 | ADVISORY | Step-1 Appendix-A re-point compositionally valid (confirmation) | RECORDED; no action — the REVISION-1 finding-1 repair stands verified | Step 1 |
| V2-4 | BLOCKER | B-4 consumed at Step 2 and graded PROVED-UNVERIFIED, but the §3.2 B-layer row omits it — a consumed input with no ledger class | ACCEPTED; B-4 (order-r layer) ADDED to the §3.2 B-layer row with its full grade (order 1 = B-3's VERIFIED-LEAN core; order r = `M6_lemma.md`, modern face O-9's OL-B → GD-3, orders ≥ 2 riding §3.1's (GR-B) on the modern path). Three-class completeness restored | §3.2 |
| V2-5 | BLOCKER | Step 14's (ADM) hypothesis (O-9 r2) has no ledger home — a consumed condition in no class | ACCEPTED; new §3.1 [M] row **(ADM)** (ledger-admissibility of the census datum; PROVED automatic at orders ≤ 1; at orders ≥ 2 open but p-free and per-datum decidable — borderline [M]/[T], kept [M] for honesty); carried by **(ROOT-C)(H3)**; enters Step 14 (CEN-W/CEN-J) hence Step 18's K3 census half. Step 14 + §1 headline synced | §3.1, Step 14, §1 |
| V2-6 | BLOCKER | clause (R)'s self-loop formula unquantified — at e = 1 the denominator vanishes, contradicting ℛ-membership and pole-freeness; no step excluded e = 1 | ACCEPTED — the real bug; adjudicated as displayed in the headline above: **e ≥ 2 forced** (L4 strict descent + K_1 = (0)); proof DISPLAYED as **(SL≥2)** at Step 5 with the consumer audit (Steps 5/17/18 consume only through O-12's e ≥ 2-scoped theorems; no consumer instantiates e = 1); §1 formula quantified with the exponent bound e(e+1)/2 − 1 ≥ 2 | §1, Step 5, Step 19 |
| V2-7 | ADVISORY | roster consumer annotations incomplete: MacLane entry omits Step 9 (and Step 9 unpinned); GMN consumer list omits Step 15 | ACCEPTED; MacLane entry + Step 9 now pin the exact loci (Def 4.1 + Thm 4.2 = the (V1) frame-semantics pin, LITUNIT §4 MATCH; no further MacLane theorem enters O-14a′); GMN entry gains Step 15 (K-FACT = Thms 1.15/1.19 + 3.1/3.7, loci already pinned) | Step 9, §4 items 1/2 |

**The completeness invariant, re-run after these repairs** (the §7 closing charge —
"every named pin/flag has exactly one ledger home" — which V2-4/V2-5 again showed is
the failure-prone one): the (ROOT-C) hypothesis list is now (H1) (GR-B) ≥ 2, (H2)
(FRESH), (H3) D-12r + (E-N) + (ADM), (H4a) (R1)–(R4), (H4b) (UB-X) — exactly the
seven §3.1 [M] rows, none clause-misattributed; (S3) is the one declared seam with a
NON-mandatory home (annex A-1), displayed as such at both its touch points.

**What VC3 (the next end-to-end pass) should check first:** (1) the (SL≥2) display
against O-12 rev 4 (is the three-step forcing airtight, and is the consumer audit
complete?); (2) the (H4a)/(H4b) per-clause attribution in (ROOT-C) against Steps
16/18/19 (does any OTHER §3.1 row leak across clauses the same way?); (3) the (S3)
scoping against D-11 r2 §3 (is the monic/projective split verbatim-faithful?).

**Standing note on status syncs:** REVISION 2 makes NO status changes — VC2 was a
composition-only pass; leaf statuses remain as synced at REVISION 1 (the c43b13b
harvest + the recorded in-flight r2/r5 landings). The in-flight passes (D-11/O-11
pass 2s, CU-1 gap-check, O4T clean pass, O-9 re-pass) resolve at the next harvest
and their rows carry unchanged.

— REVISION 2 complete. The body above is the operative composition; VC3 runs on this
document as a whole.

---

## 9. REVISION 3 (2026-08-02 night, unit ROOT r4) — disposition of VC3, the Phase C end-to-end pass 3

**The pass.** VC3 = the third end-to-end verification and the first MODEL-DIVERSE one
(Claude/Fable, fresh context — VC1/VC2 were Codex; read the ROOT document ONLY, no
leaf records; `lean/notes/openmath/VC3_root_fable_verify.md`). Verdict:
**COMPOSITION-GAPS** — 4 blockers (B1–B4) + 4 advisories (A5–A8). The headline is
what VC3 CONFIRMED: "under all five hypotheses jointly, the composition proves
(ROOT-C) quantifier-for-quantifier from the leaves' declared statements + ledger
rows; every defect found is attribution/ledger integrity, not mathematics missing
beyond the displayed hypotheses." Explicit passes: acyclicity edge-by-edge over all
20 steps (incl. the 17 ≺ 18 ≺ 18b stratification); the completeness invariant
((ROOT-C) hypotheses ↔ the seven §3.1 [M] rows, EXACTLY EQUAL); and all three §8
pre-charged spots — the (SL≥2) display internally sound with its consumer audit, the
(H4a)/(H4b) split consistent as displayed, the (S3) monic/projective split coherent.
Every finding is dispositioned below and repaired in place; per the standing charge,
NO mathematical content changed — every repair is attribution, a ledger row, or a
status sync.

**Disposition table.**

| # | class | finding (compressed) | disposition | where |
|---|---|---|---|---|
| B1 | BLOCKER | the "exact" per-clause attribution understates clause (UB): it reads "(H4a) + (H4b)" as (UB)'s full hypothesis set, but (UB) also consumes (H1)–(H3) — through Step 8 ((GR-B) at orders ≥ 2), Step 14's census ((FRESH)/(ADM)), and the (UB-X)(a)-transported layers (D-12r, (E-N)); the (ADM) row's Enters-list omitted Step 16 | ACCEPTED — the V2-2 genre in reverse (consumed but unattributed); (ROOT-C)'s attribution completed: clause (UB) consumes **(H1)–(H3) + (H4a) + (H4b)**, only (H4b) is (UB)-exclusive; Step 16's conditionality restated in full; Step 19's (UB) close synced; the (ADM) and (FRESH) rows' Enters-lists gain Step 16/clause (UB). The JOINT theorem (all five hypotheses) was never affected | §1, Steps 16/19, §3.1 (ADM)/(FRESH) |
| B2 | BLOCKER | O-8b/M14's PROVED-UNVERIFIED conditional proof is consumed (Step 16; Step 18's K3 — hence clause (R)'s mandatory path) with NO ledger row naming its pending pass — the exact V2-4/V2-5 failure class | ACCEPTED; new §3.2 row **P(O-8b/M14)** (fresh hostile pass on the M14 proof, owners Steps 16/18); Step 16's status names the pass | §3.2, Step 16 |
| B3 | BLOCKER | Σ_τ R_τ = 1 credited to Step 1 beyond Dfloor's declared statement (R_τ undefinable in the leaf's perimeter; α = R_τ needs Steps 18/18b) — a textual forward edge inside a VERIFIED perimeter, consumed by Step 19 "from Step 1" | ACCEPTED; repaired exactly as the verifier prescribed, no new hypothesis: Step 1 restated to its declared perimeter (Σ_τ α = 1 at every p + the interpolation principle; Delivers-line synced), and the identity CONCLUDED at Step 19 with the derivation displayed (Σα = 1 [Step 1] + α = R_τ ∀p [Steps 18/18b, (H1)–(H3)+(H4a)] + the principle ⇒ Σ_τ R_τ = 1 in ℚ(t)); the conditionality was already priced inside clause (R) | Step 1, Step 19 |
| B4 | BLOCKER | B-3's document-level PROVED-UNVERIFIED grade (same status shape as B-2's: Lean-verified core + June document) missing from the §3.2 B-layer row — a consumed input with no ledger class (the V2-4 class) | ACCEPTED; **B-3 (doc level)** added to the B-layer row | §3.2 |
| A5 | ADVISORY | undisplayed interface match: O-8b's law holds at δ-STABLE position classes only, but nothing displays that K3-c's δ > 1 pools are δ-stable — if one were not, (UB-X)(b) would leak into clause (R) | ACCEPTED as an honesty display: the presumption is now DISPLAYED at Step 18 and recorded as an audit note on the §3.1 (R1)–(R4) row (the match is asserted at the D-c interface, not proved here); the match display (or a re-scope) rides the next O-11/O-8b touch | Step 18, §3.1 |
| A6 | ADVISORY | three consumer-list gaps: (i) GMN roster omits Step 11 (CU-2t consumes Cor 1.20/3.8 directly); (ii) the D-12r row omits Steps 2 and 19 (T-6's TB-CAP conditionality; the bracket consumes T-6); (iii) the (FRESH) row omits Step 10 while Step 10's Delivers-line names "the (FRESH) consumption site" | ACCEPTED; all three lists completed ((iii) resolved as CONSUMPTION at CU-1's step — the row itself prices (FRESH) "at the GD-2/CL-13 vertex-law layer = CU-1's step content"; clause (SQ)'s (H1)–(H3) attribution already covered it) | §4 item 1, §3.1 D-12r/(FRESH) |
| A7 | ADVISORY | OL-O12-1 (Step 5's contingent escape flag) has no ledger home, against the §7 closing standard | ACCEPTED; §3.3 row added (unfired, consumed by nothing — homed for the invariant) | §3.3 |
| A8 | ADVISORY | Step 19 discharges T-U's §U.SQ.6 kernel ledger by the ASSERTED-not-displayed claim that it equals the Steps 1–18b roster; a fresh reader cannot check it | ACCEPTED at the honest-marking option: Step 19's parenthetical now states the claim is asserted, and a §3.3 audit row owes the row-by-row display table (per-item pointer §U.SQ.6 → step/eviction/annex) | Step 19, §3.3 |

**Status syncs applied with the repairs** (the 2026-08-02-night harvest, ledger
7b28562 — "THE FIVE OWED PASSES" section): **CU-1 = VERIFIED, leaf #5** (r5 gap-check
GAPS-CLOSED 0/0, commit 5329a4e); **O-10 = VERIFIED at scope, leaf #6** (pass 2
model-diverse SOUND-WITH-GAPS, math airtight, 5296528; two minor gaps ride a §3.2
doc-touch row) — **VERIFIED = 6: O-13, O-12, Dfloor, GD23, CU-1, O-10** (headline +
(ROOT-C) proof-status synced 4 → 6; the discharged CU-1/O-10 §3.2 rows retired).
Wave-14 rows synced: **O-9** pass 2 UNSOUND (af2293e: the rev-2 (ADM) class-vs-value
attainment equivalence refuted by an r = 1 countermodel) → **r3 with the
VALUE-attained (ADM) reading** (§3.1 (ADM) row annotated); **CUC/CU-2t** pass 1
UNSOUND (b9d1d70: the Θ^τ ν-blindness critical + 9 gaps) → **CU-2t R2** (Definition
RC displayed; the (T-DEC)/(T-VERD) pricing honesty-corrected — the mandatory-path
residue GREW by two GD-4 rows, folded at Step 11 + the §3.3 GD-4/GD-6 row per the
R2's F4 charge), re-pass owed; **O4T** pass 3 SOUND-WITH-GAPS,
ZERO criticals (ed413ae) → **r4 (two one-liners)** + one confirming pass to
the bar. Also recorded (round-3 events pre-dating VC3, rows previously stale): D-11
pass 2 → **r3** (8a0786c, honestly LAYERED) and O-11 pass 2 (V32) → **r3** (7aef1b9,
tier 2 split into H-1..H-4), pass 3s owed. Nothing in this revision upgrades any
leaf beyond the ledger's own adjudications; it corrects this document's composition
bookkeeping and syncs recorded statuses.

**The completeness invariant, re-run after these repairs** (the failure-prone one
again — B2/B4 are its V2-4/V2-5 class, and B1 is its per-clause face): the (ROOT-C)
hypothesis list is unchanged — (H1) (GR-B) ≥ 2, (H2) (FRESH), (H3) D-12r + (E-N) +
(ADM), (H4a) (R1)–(R4), (H4b) (UB-X) — exactly the seven §3.1 [M] rows; the
per-clause attribution is now: (0) unconditional; (SQ)/(R) ← (H1)–(H3), (R)
additionally ← (H4a); (UB) ← (H1)–(H3) + (H4a) + (H4b); (H4b) (UB)-only. Every
consumed PROVED-UNVERIFIED input now has a named §3.2 pass (O-8b/M14 and B-3-doc were
the last two missing); every named pin/flag has exactly one ledger home (OL-O12-1 was
the last).

**What VC4 (the next end-to-end pass, Codex, toward the ≥ 2-consecutive-clean bar)
should check first:** (1) the B3 repair — does Step 19's displayed Σ_τ R_τ = 1
derivation consume only Steps 1/18/18b at their declared statements, and is Step 1's
restated perimeter now exactly the Dfloor leaf's?; (2) the completed (UB) attribution
against Steps 8/14/16 (is (H1)–(H3) + (H4a) + (H4b) now exact, neither under- nor
over-attributed?); (3) the A5 presumption at Step 18 (is the δ-stable audit note
scoped so that clause (R)'s (H4a)-only attribution is honest as displayed?); (4) the
completeness invariant, per standing §7/§8 experience.

**Concurrent in-flight events recorded at REVISION 3 close** (the wave-14 repair
commits landed by parallel units while this revision was being written; body statuses
are AS OF the 7b28562 harvest, with bracketed landed-at-close notes at the affected
rows): **O-9 r3** (460ea59 — (ADM) redefined VALUE-attained; automaticity rescoped
r = 0 automatic / r = 1 displayed decidable inequality / general r ≥ 1 withdrawn; K6
falsifier 0 = 0 exact at the pass-2 countermodel); **CU-2t R2** (unit of record
567814d — Definition RC; Θ^τ carries ν's announced pair; the +2 GD-4 rows pricing);
**O4T r4 + O-10 r2** (3956500 — display fixes, cores byte-stable; O-10's VERIFIED
stands per the wave-14 ledger). Confirming passes owed: O4T (acceptance), O-9 pass 3,
the CU-2t R2 re-pass. Bookkeeping note (the REVISION-1 4e03512 precedent): commit
9136564's staging sweep captured this revision's in-progress body repairs alongside
the wave-14 ledger fold; THIS commit is the revision's unit of record.

— REVISION 3 complete. The body above is the operative composition; VC4 runs on this
document as a whole, and the ≥ 2 consecutive-clean counter remains at ZERO.
