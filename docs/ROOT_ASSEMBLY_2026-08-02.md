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
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` final sections, commit c43b13b). What
exists is: an acyclic composition (acyclicity now holds edge-by-edge: the Step-1 edge
REMOVED by re-pointing to Dfloor's self-contained Appendix A, the D-11/O-11 cycle
STRATIFIED as Step 17 ≺ Step 18 ≺ Step 18b) in which every step is a named leaf with an
on-file proof, FOUR of the leaves VERIFIED through the campaign's two-pass
model-diverse bar (O-13, O-12, Dfloor, GD23; the earlier CU-1 adjudication was
premature — corrected at the ledger, r5 in flight), the rest PROVED-UNVERIFIED with
their pending passes NAMED, and the genuinely open mathematics confined to §3.1: the
two heavy items — **(GR-B)** at OM orders ≥ 2 and **(FRESH)** — both pinned to printed
literature statements and priced at a single lemma layer, plus the smaller displayed
rows ((R1)–(R4) with the clause-(UB) residue (UB-X), D-12r, (E-N)). **THE THEOREM AS
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
> descend = strictly smaller child, self-loop of size e = geometric resummation
> 1/(1 − q^{−(e(e+1)/2 − 1)}) — whose state menu, coefficients, and pivots carry NO
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
> (τ-irr) perimeter) and (E-N); **(H4)** for clause (UB) only: (R1)–(R4) AND the
> clause-(UB) residue (UB-X) (the per-leaf O_δ re-base audit + position-class
> exhaustion + aggregation commutation — §3.1).
> Then for each n ≥ 2 and each splitting type τ of degree n there is a single
> R_τ ∈ ℛ such that clauses (0), (SQ), (R) hold at EVERY prime p including every wild
> p ≤ n, and clause (UB) holds. Without (H4), what is proved of (UB) is exactly the
> Step-16 scope: the GD/census layers hold over an arbitrary absolutely-unramified
> complete DVR, and the alphabet law (F_{p^δ}-linearity + a_δ = δ·a₁) holds at
> δ-stable position classes.
> **Proof status of the implication itself:** it is the §2 composition — four leaves
> VERIFIED, the rest PROVED-UNVERIFIED with named pending passes (§3.2) and displayed
> transcription debts (§3.3). The [V]/[T] rows are AUDIT debts on the proof of this
> implication, not additional mathematical hypotheses of its statement; the
> implication is therefore itself PROVED-UNVERIFIED (never consumed by an acceptance
> claim) until §3.2/§3.3 empty and the end-to-end passes land. (ROOT) = (ROOT-C) +
> discharge of (H1)–(H4).

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
DELTA-2 §D2.3 — the K-RUN-C composition replaced the joint induction). Standing
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
and is NOT consumed here. The edge is removed, not waived.] Hence Σ_τ α(n,τ;p) = 1 at
every p, and a rational function agreeing with 1 at infinitely many arguments is 1:
Σ_τ R_τ = 1 in ℚ(t). (D-4) the degree-1/0 floor: type {(1,1)} density 1 decided at
k = 0; empty-convolution unit conventions (C0)–(C2).
Status: **VERIFIED — leaf #3** (pass 1 Codex V22 CLEAN SOUND, 0 criticals, commit
604621f; pass 2 fresh Fable, model-diverse, 0 criticals, commit bdc996a; adjudicated at
ledger dbccbc1; falsifier `verification/openmath/dfloor_checks.py` ALL PASS). Three
minor gaps ride the next doc touch. Displayed residue: the **BASE-1(f) fence** — the
classifier-side (algorithmic) half at n = 1 is fenced OUT to the classifier steps below.
Consumes: LIT-2 (defectlessness; the K-11/M16 audited e·f bridge), LIT-8c
(resultant/Vandermonde — carries Appendix A's ns-null), standard measure theory with
displayed statements (Folland-grade; §4 roster). NOTHING from any later step.
Delivers to the root: clause (0), the bracket shell of (SQ), and the Σ_τ R_τ = 1 half
of (R).

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
pins (§4). The (S6b′) clause and the landing flank are INTERNAL — closed inside the
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
Status: **ZERO-CRITICAL PASS 2, NOT YET VERIFIED — r5 IN FLIGHT** [REVISION 1 status
sync] (arc: V27 UNSOUND, core repairable → rev 2 structural repairs (N-free induction,
interior/terminal split, construction-before-recovery, declared pins) → V29
SOUND-WITH-GAPS 0-critical → rev 3 (consumption accounting only; induction
byte-stable) → pass 2 fresh Fable, 0 criticals, 7 consumption-accounting/display gaps,
commit 252f34c → [the wave-10 VERIFIED adjudication at d730669 was CORRECTED AS
PREMATURE at the ledger, commit 110f308] → rev 4 light repairs, all 7 gaps, cores
§§1–3 byte-identical (commit 8ab8ca6) → gap-check: GAPS-REMAIN → **rev 5 dispatched,
in flight at the 2026-08-02 harvest** (commit c43b13b)). The mathematical core
(N-freeness, creation-first, split-exhaustiveness) is confirmed by the pass-2 report;
what remains is accounting/display closure. Primary gate: the depth-3 falsifier ran
BEFORE rev 1 and SURVIVED.
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
re-labels mapped to proved homes (commit a9f294c); **CU-2t is PROVED** (CUC §9, unit
D3CU2t, swept into 254d4de) conditional on P(O-2a r5) + TB-CAP's D-12r perimeter + the
GD residue, zero new open inputs; the two terminal engine-bookkeeping rows
(T-DEC)/(T-VERD) are displayed GD-4-family instances. Pending: the hostile pass on the
CUC record + CU-2t (owed, §3). The quarantined Corollary CU-2t-deep (the GD-8 exact-key
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
line-by-line audit twice.
Consumes: Steps 1/10/11 + GMN Cor 4.19 + the O4T import inventory (§4).
Delivers: the undec(k) → 0 clause of (SQ) — unconditional at n ≤ 3, conditional on
(AGR) (= CU-2 + CU-4 + Cor 4.19, all on file above) at general n.

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
(ADM) admissibility hypothesis displayed (automatic at orders ≤ 1), and JUNCTION-PIN's
PROVED label WITHDRAWN — honestly rescoped as OPEN, absorbed into **(FRESH) as its
clause (c)** (the telescope consequence is proved GIVEN the clause). The sound-listed
core is byte-stable. With the repair on file the row is again honestly [V]:
re-pass owed.
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
Status: **PROVED-UNVERIFIED** (commit 3e9f199; ledger grade "PROVED IN FULL SHARPER");
verify pass 1 CLEAN (commit ec5e9a1: 0 criticals, 0 load-bearing gaps; 2 declared-cite
gaps + 3 precision notes). Pending: the second (model-diverse) pass of the dual bar.
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
**PROVED-UNVERIFIED conditional on (R1)–(R4)** (expected mechanical, nobody has written
it — §3 ledger); N8 numerics exhaustive (199,723 alphabets, 17 fields, 0 violations).
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
(UB) of (ROOT-C) is conditional on (R1)–(R4) + (UB-X), exactly as §1 displays.
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
leaf labels; K2 ← O-12 at 𝔅_n + D-11 PACK SIDE (= Step 17's tranche, never M2); K3 =
[1v]-FULL value correctness ASSEMBLED from T-7s + O-9's census + O-8b (arbitrary-DVR);
K4 ← Dfloor/D-15/CU mass semantics. Every consumption displayed (the unit's 20-row
table).
Status [REVISION 1 status sync]: **PROVED-UNVERIFIED (ASSEMBLED), r2 owed** — commit
3fc8f52; tier-1 residue exactly **{(GR-B), (FRESH), CU-2t, D-11 first tranche}**;
verify pass 1 NOT ACCEPTED AS STATED (commit a7ede72 — 1 critical: (M6b)(iii) consumed
at K4-CYL/row 4 but priced into no tier, so the "exactly FOUR" residue display is
unsupported as written, + 8 gaps incl. reductions asserted by pricing-citation; the
equivalence directions and the walk itself CLEAN; drainage verifiably unconsumed) →
O-11 r2 owed. Falsifier ran FIRST: `verification/openmath/o11_seriestie_check.py`
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
(GR-B) conditionality, §3.1); **(S2)** = the O-11 composition datum ← Step 18. (r1) is
the uniqueness pivot (Step 17). With Step 18 this closes the chain
α = (tree series) = R_τ.
Status: **PROVED-UNVERIFIED, r2 owed** (same D-11 record and pass-1 verdict as Step
17; the M2-specific pass-1 gap — the (O2′) balance-equation leg underderived — rides
the r2).
Consumes: Steps 14, 17, 18 — all earlier; the (GR-B)/(FRESH) rows through (S1).
Delivers: the α = series identification; with Step 18, the α(n,τ;p) = R_τ(p)
evaluation clause of (R).

### Movement V — the closer

**Step 19 (T-U + K-13 + O-12 — the squeeze fires at every prime).** THEOREM U
(VERIFIED-DUAL, conditional on its displayed §U.SQ.6 ledger — which IS the set of
leaves above) takes: the bracket at every finite level (Step 1 + D-15 + T-6), drainage
(Step 13), the evaluation chain — **attribution exact [REVISION 1, finding 11]: Step
18 delivers series = R_τ (O-11); Step 18b delivers α = series (D-11 M2); TOGETHER they
deliver α = R_τ — neither alone does** — and the pole-free specialization at every
prime power (Steps 4 + 5 + 17) — and squeezes: decided_τ(k)/p^{nk} → R_τ(p) = α(n,τ;p)
at EVERY prime including wild, with Σ_τ R_τ = 1 from Step 1. Clause (UB) from Step 16
at its displayed conditional scope ((R1)–(R4) + (UB-X)). This is exactly (0) + (SQ) +
(R) + (UB-conditional): **(ROOT-C)**, quantifier-for-quantifier. ∎ (conditional
exactly on the (ROOT-C) hypotheses (H1)–(H4); the §3.2/§3.3 rows are audit debts on
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
verification cycles, ROOT ASSEMBLY}"), EXPANDED to every named pin/flag a reader of §2
encounters. Character classes: **[V]** verification-pass debt (a proof is on file; a
named fresh-context hostile pass is owed — no new mathematics expected unless the pass
finds some); **[T]** transcription debt (content pinned to printed sources or existing
proofs; writing/auditing owed, no new mechanism expected); **[M]** genuine open
mathematics (no proof on file). The CUC §0 pending-verdict registry
(`lean/notes/openmath/CU_cluster_phaseB.md` §0) is the live key for the P(·) items.

### 3.1 Genuine open mathematics [M] — the honest mathematical distance

| item | statement | owner | notes |
|---|---|---|---|
| **(GR-B) at OM orders ≥ 2** | the anchored-march residue-structure package (GD-2/GD-3's one open input): the frame tie + residual-dictionary march at orders ≥ 2, modeled on printed FGMN Thm 4.2 (both pairings), with the properness proviso | GD-1/GD23 arc (verify passes: the GD23 verification cycle continues at orders ≥ 2) | order ≤ 1 PROVED over an arbitrary complete DVR (inside VERIFIED leaf #4); the wave-10 ledger grades the ≥ 2 layer "FGMN-pinned, transcription" — every target statement is pinned to a printed theorem (LITUNIT §7), but the composed march at ≥ 2 is unwritten: honestly [M] until written and passed. Enters Steps 10 (CU-1's step), 14 (CEN-W), 16, 18 (K3) |
| **(FRESH)** | the joint-with-parent level-determinacy separation clause (O-9's named open), priced at the GD-2/CL-13 vertex-law layer = CU-1's step content | O-9/CU-1 layer | enters Step 14's joint census CEN-J, hence Step 18's K3. Numerically unviolated (8.2M boxes) |
| **(R1)–(R4)** (O-8b's base) | the T-1 stage-tower laws re-proved verbatim over O_δ = W(F_{p^δ}) | O-8b (M14's conditional proof closes given them) | expected mechanical ("nobody has written it" — tree O-8b); N8 exhaustive. Borderline [M]/[T]; kept here for honesty. Enters Step 16 |
| **D-12r** | TB-CAP's (τ-irr) completeness perimeter: the D4R.0-K(c) verdict-pin residual | [3t] VP owner (tree D-12r) | perimeter-conditional wherever TB-CAP is consumed (Steps 3, 11, 12); displayed, not discharged |
| **(E-N)** | O-1thr Theorem 3(c)'s exhaustion caveat | O-1thr package | OPEN, scoped, touches CU-4 through Thm 3(c) (risk row R2 of the O3adj display); NOT consumed by the mandatory path elsewhere |
| **(AGR) = OL1-ii at general n** | the drainage agreement seam: canonical termination + acceptance below a finite N(f) | O-4/O4T (TR-OM) | ASSEMBLED from CU-2 + CU-4 + GMN Cor 4.19 (all on file), so its residue is exactly the [V] debt of those pieces — listed here because until those passes land, general-n drainage is conditional; n ≤ 3 unconditional (O4T Thm N3) |

### 3.2 Verification-pass debt [V] — proofs on file, passes owed (named)

| item | what is owed | owner |
|---|---|---|
| **P(O-2a r5)** | fresh hostile pass on O-2a rev 5 (core thrice confirmed; V25 arc) | O-2a (Step 7) |
| **P(O-1thr r4)** | fresh hostile pass on O-1thr rev 4 (V24's criticals repaired; sloped/sheared pin stands) | O-1thr (Step 6) |
| **P(O5t r3)** | fresh hostile pass on O5triple rev 3 (V23 0-critical arc) | O5triple (Step 12) |
| **O-10 pass 2** | the second, model-diverse pass of the dual bar (pass 1 CLEAN, commit ec5e9a1) | O-10 (Step 15) |
| **O4T repair + pass 2** | the in-flight Fable pass 2 (untracked working-tree record, NOT adjudicated) returned UNSOUND: 1 localized critical (N3-BRACKET terminal "=", false for N ≥ 2; inequality + density form survive, nothing downstream consumes it) + 4 gaps (import inventory incomplete) — repair round + re-pass owed | O4T (Step 13) |
| **O-9 repair + re-pass** | pass 1 NOT ACCEPTED (commit c17777f): repair the census exponent E′'s left-tail ledger (machine-countermodeled) + the JUNCTION-PIN label; the verifier's sound-list preserves the reduction's shape | O-9 (Step 14) |
| **D-11 verification cycle** | pass 1 on the MASS-ID attempt (commit 0cae7d8) | D-11 (Step 17) |
| **O-11 verification cycle** | pass 1 on the SERIES-TIE assembly (commit 3fc8f52) | O-11 (Step 18) |
| **CUC + CU-2t hostile pass** | pass on the consolidation record + the CU-2t lemma (CUC §9) | CUC (Step 11) |
| **GD23 gap-9 light repairs** | the 9 justification gaps of the accepting pass 2 (4d109b9; heaviest: (GR-B) operator domain "side-supported", exact-match display's R-factoring, TIE policy pin at summary layer) ride the next doc touch — adjudicated non-blocking | GD23 (Step 8) |
| **CU-1 gap-7 display repairs** | the 7 consumption-accounting/display gaps of the accepting pass 2 (252f34c) — same class | CU-1 (Step 10) |
| **Dfloor 3 minor gaps** | ID reduced-rep, ADD induction coprimality, TRANSFER sum-regularity — ride the next doc touch | Dfloor (Step 1) |
| **K-12 faithfulness-audit record** | the Lean `undec`/`hExhaustP` vs mathematical-classifier audit (DELTA-1 §D1.5(g)); grade held pending | K-12/n = 2 anchor |
| **End-to-end passes on THIS document** | ≥ 2 consecutive clean end-to-end passes, ≥ 2 models, verifiers who saw none of the per-leaf rounds (tree §4 Root criterion) | Phase C |

### 3.3 Transcription/audit debt [T] and named pins/flags

| item | content | owner |
|---|---|---|
| **GD-5 residue: the S-1 audit** | the one-page composition note + machine transcription audit (O-1thr machine ↔ O-2a stage interface F.0–F.2 at order 1) + the degree-g > 1 KEY1 generalization (same method) | GD-5 (D2.6 step 2) |
| **GD-4 / GD-6 engine-bookkeeping units** | emission/record discipline (W1–W5, (c0), AUX band; K-OB-E's GMN Def-3.9 arithmetic is the one semantic clause) and run-decomposition conformance; proof-by-construction routes on record; CU-2t's (T-DEC)/(T-VERD) rows are displayed GD-4 instances | GD-4/GD-6 owners |
| **GD-7 flags: (GMN-COH)/(R-0)/(R-1)/(R-2)/(R-3)** | O5triple's five citation-grade flags (sprouted-type dissection, flow coherence, order-0 anchor, ADEQ read-back, representative lookup) — one GMN §2.1/§3/§4.1 reading session covers them; NOT covered by the executed LITUNIT | GD-7/literature unit (Step 12) |
| **GD-8 order ≥ 2** | the exact-key polygon seam beyond order 1 (order-1 proved, falsifier-covered); expected verbatim over GD-2's frame tie | GD-8 |
| **(KP)/(KPirr) beyond order 1 + properness proviso** | GD-1's representative-admissibility clauses; properness a genuine side condition only at e·g = 1 refinement reads (FGMN Lemma-5.3 discharge displayed) | GD-1 |
| **Declared pins (P-ROOT)/(P-KEY)/(FR≡)** | CU-1's three declared pins replacing silent cross-brief glue; (FR≡) has refutable order-2 content = the gate's coherent-convention finding | CU-1 (Step 10) |
| **Sloped/sheared convention pin** | O-1thr's window-height convention (the depth-2 falsifier forced it; 41,720/0 vs 7,472 violations unsheared) | O-1thr (Step 6) |
| **(I-τ) + K-LOC interface** | the adapted-cell → engine-stratum presentation for O-10's Theorem 2 (K-LOC = M07 OL-3: continuation reads of branch j = OM reads of f_j up to cell-constant normalization) | GD families / O-10 consumers (Steps 15, 18) |
| **(S1)/(S2) seams of D-11 M2** | (S1) = GD-3-FULL/O-9 hand-off; (S2) = the O-11 composition datum — both discharged BY Steps 14/18 once their passes land; displayed to keep the acyclicity visible | D-11 (Step 17) |
| **OL-O12-2 data pass** | the finite transcription/correspondence pass identifying the complete degree-3 table as an (O3) member of 𝔅₃ (math half closed at D-11) | O-12/D-11 |
| **BASE-1(f) fence** | Dfloor's classifier-side n = 1 clause, fenced to the classifier steps (served by Steps 6–13's package) | Dfloor/CU |
| **LC-COH** | the displayed open note from the O-3 clause-3 re-key — CONSUMED BY NOTHING (kept for honesty) | tree D2.1 line 1 |
| **(REP-IRR)** | the unpinned literature pull behind the QUARANTINED Corollary CU-2t-deep (GD-8 corner) — consumed by nothing mandatory; flagged to the literature unit | CU-2t/literature unit |
| **W3 carrier note** | the τ-irr seam object is a PAIR, not an 𝔈-concatenation (CU-2t display; convergent with CU-1's split) | CU-2t |
| **LIT-1 printed-TAMS pagination** | the standing GMN confirmation duty (LITERATURE-CONDITIONAL until confirmed); one session with the printed TAMS covers it + the GD-7 flags | literature unit |
| **LIT-3 numbers + Mathlib probe** | Neukirch II §4 Prop 4.6 / Serre LF I §6 numbers to confirm at declaration; probe `HenselianLocalRing` first | literature unit (Step 12) |
| **LIT-8 per-use-site transcriptions** | LIT-8a..8e split (DELTA-1 §D1.5(d)); exact numbering owed at each declaration site (O4T's inventory did this for its own sites; Dfloor displays statements) | per consumer |
| **Item-27/28 Lean statement repairs + O-14d instance population** | PARKED engineering (Lean statement fences; the wave-D carrier population) — outside the math criterion by DELTA-1 §D-10 | Lean side, post-math |

**What is NOT on the ledger (evicted from the mandatory path, recorded):** O-2b/OB1
(trace correspondence), OB2/CU-6 (σ-invariance under ∼_OM — the DELTA-3 audit: D-11
needs per-box lift uniformity instead), LIT-5/BNS entirely (zero root-side touch-points),
K-OB-C (Okutsu proximity), D-16 (δ-tier execution transport), O-6/O-7/O-8a (track
count/weight charge/linear rates) — ALL route R-QNT, needed only if explicit rates are
elected. htameFE/palindromy + the projective bridge are ANNEX (A-1/A-2).

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
   Cor 4.19 (termination); Defs 4.11/4.12/4.15. Status: LITERATURE-CONDITIONAL
   (printed-TAMS pagination confirmation owed — §3.3). Consumed by Steps 7, 8, 12, 13, 14.
2. **[ML] MacLane**, *A construction for absolute values in polynomial rings*, Trans.
   AMS 40 (1936) 363–395. Pinned (LITUNIT, re-typeset caveat displayed): Thm 4.2 (the
   (V1) multiplicativity), Def 4.1, Thm 10.2, Lemma 10.1, Lemmas 11.1–11.2, Thm 12.1,
   Cor 12.2 (commensurable hypothesis automatic here). Consumed by Steps 6, 8 (and
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
| `o11_seriestie_check.py` | Step 18 (incl. Finding F1's test at the REAL pack) | 38/38 PASS; n = 2 true triple identical in ℚ(q) |
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

Immediate dispatch order (inherited from §D3.6, updated by this document): the O-9 E′
repair; the O4T N3-BRACKET repair (both localized); the D-11 and O-11 pass-1s; the CUC/
CU-2t pass; the three registry passes P(O-2a r5)/P(O-1thr r4)/P(O5t r3); O-10's pass 2;
then the GD order-≥ 2 campaign for (GR-B)/(FRESH) — the last genuine mathematics
between this assembly and the theorem.

— ROOT ASSEMBLY complete, 2026-08-02. Composed at HEAD d730669 + the recorded
in-flight events (O4T pass 2, untracked). Every §2 grade traces to a named commit or
pass record; nothing above upgrades any leaf's status.
