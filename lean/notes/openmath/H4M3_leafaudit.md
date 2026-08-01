# H4M3_leafaudit — the (UB-X)(a) per-leaf O_δ re-base audit (unit H4-M3, executed)

**Unit:** H4-M3 (`lean/blueprints/HDISCHARGE_H4.md` §M row 3; charge = §3.1's table).
**Prover:** Fable H4-M3, HDISCHARGE_H4 division, 2026-08-08.
**Authority:** `docs/ROOT_ASSEMBLY_2026-08-02.md` Step 16 (the (UB) step: its honest-scope
display and Consumes-list) + `docs/MATH_COMPLETION_TREE_2026-08-01.md` node D-3
(UNRAM-TRANSFER) + the LITUNIT pins (`lean/notes/openmath/LITUNIT_2026-08-01.md`,
`docs/GMN_citations.md`, `docs/AXIOM_FAITHFULNESS.md`).
**Gate:** hostile pass ×1 (record §5); **no numerics** (none run — every numeric fact
cited below is a sealed, existing suite). No `.lean` file lands with this unit (the H4
Lean faces are fenced H4-F1/F2/F5/F6; blueprint §L.5).

---

## 0. Verdict summary

The nine charged rows are executed below (§2.1–§2.9), plus **one row FOUND MID-AUDIT
and ADDED** (§2.10), per the standing rule (rows added, never absorbed). Classes are
the §3.1 charge's: **(i)** stated-general already · **(ii)** p-free symbolic (no base)
· **(iii)** mechanical re-base (proof template carries; delta written) · **(iv)** real
content (proof written or a named lemma opened). No row is closed by "the theory
transfers".

| # | leaf | expected (§3.1) | **audited class** | status |
|---|---|---|---|---|
| 1 | Dfloor D-1/D-2/D-4 (Haar floor) | (iii) mechanical | **(iii)** | CLOSED |
| 2 | K-DICT (O-2/O-2a) | audit/split | **(iii)** (core (i)) | CLOSED |
| 3 | K-RUN (O-3 ⊕ O-2b) | audit/split | **(iii)** — with the realizer supply CARVED OUT to row 10 | CLOSED (row's own text) |
| 4 | K-HALT/ASSEMBLY (O-5/O5triple) | audit | **(iii)** | CLOSED (+1 displayed source correction) |
| 5 | drainage (O-4/O4T; AGR seam) | audit | **(iii)** | CLOSED |
| 6 | CU cluster (CU-1..4, CU-2t) | audit | **(iii)** | CLOSED (CU-3 leg → row 10) |
| 7 | O-1thr (D-14/D-15 cylinder laws) | (iii) mechanical | **(iii)** | CLOSED |
| 8 | O-10 (K-COUNT/K-JAC) | audit | **(iii)** | CLOSED |
| 9 | LIT-4/(OM-SAT) | **(iv) expected** | **(i)** — printed GMN scope already covers K_δ | CLOSED (+ MECH roster-sync duty) |
| 10 | **ADDED: O-14a′ run-realizer supply (RRE) at ambient F = F_{p^δ}** | — (not on the §3.1 list) | **(iv)** | **OPEN — Lemma RRE-δ (displayed, §2.10)** |

**Completion-criterion adjudication (blueprint Codex fold, finding 9):** (a) counts
DISCHARGED only when every row is class (i)–(iii) CLOSED or its class-(iv) lemma is
PROVED. Rows 1–9 are (i)/(iii) CLOSED; row 10 is class (iv) with **Lemma RRE-δ OPEN**.
Therefore **(UB-X)(a) stays OPEN, with Lemma RRE-δ as its displayed residue, and
H4-M6/H4-M7 stay BLOCKED on it.** Headline inversion, on record: the blueprint's
expected residue (LIT-4) CLOSES — GMN's printed standing scope is a fixed finite
extension K/ℚ_p, which contains every K_δ — while the actual residue is the
run-realizer seam that `O3design_phaseB_attempt.md` §2 had explicitly flagged
"for D-3": at δ > 1 the consumed prime-field collapse is structurally unavailable and
the compiled support clause (CR2) is REFUTED-AS-STATED (the F₉ countermodel, i.e. an
exact (p, δ) = (3, 2) instance), with the corrected law standing as O14ap
Conjecture 5.4.C. The verdict is robust: even if the hostile pass demotes row 9's
class-(i) closure (see its displayed residue), (a) is already held OPEN by row 10.

---

## 1. Conventions and ground rules

**Bases.** O_δ := W(F_{p^δ}) (δ ≥ 1 absolute — the MovesRBase BASE-INDEX CONVENTION,
matching REL.2(e2)); K_δ := O_δ[1/p]; residue field F_δ := F_{p^δ}; q := p^δ (written
q_δ where contrast with a generic q is needed); maximal ideal m = pO_δ. Since
K_δ/ℚ_p is unramified: the normalized valuation v has v(p) = 1, the value group is ℤ,
and π = p is a uniformizer — **all integer threshold/level/weight arithmetic of the
leaves carries with the SAME constants**. Where a statement is free of the specific δ
it is displayed over an arbitrary W(F_q), F_q an arbitrary finite residue field (the
blueprint §2 one-theory discipline); base ℤ_p is the q = p instance.

**The mutatis-mutandis rule (REL.1; blueprint §2 "Honesty on 'verbatim'"), binding on
every row:** every residue-theoretic OBJECT (base residue field, residual polynomials,
tower fields, graded pieces, attainable images, irreducibility conditions, residue
bases) is RECONSTRUCTED over F_q, never obtained by substituting a cardinality; only
the base-independent skeleton (coefficient order, unitriangular polynomial identities,
valuation geometry, additive equal-fiber counting) carries over as written. The LAWS'
statements are verbatim; the objects are rebuilt.

**Scope discipline (what closure means here).** This audit settles each leaf's
BASE-dependence: the re-based statement is displayed, and the proof is classified
(i)–(iv) with the delta walked. It does NOT discharge the leaves' standing
conditionality at base ℤ_p (pending hostile passes P(·), the OL-* engine-seam lemmas,
(AGR), (E-N), D-12r, TB-CAP's perimeter, the (H1)–(H3)/(H5)–(H9) groups): those rows
are INHERITED IDENTICALLY at both bases and are already carried by Step 16's honest
conditionality display ("the (UB-X)(a)-transported dictionary/CU/drainage layers carry
D-12r/(E-N) — none of these evaporates over O_δ"). A row closes when its re-base adds
NO NEW base-touching content beyond the named inherited rows — and every inherited row
consumed is NAMED in place, never silently absorbed. Conversely, content owned by
(H4a) — the (R1)–(R4) stage-tower re-proofs, i.e. the O-8b ALPHABET SLICE of the D-3
collapse — is pointed at unit H4-M1/M2, not re-audited here: the D-3 collapse
(adjudicated at the GD dispatch) is exactly "per-leaf scope hygiene [THIS unit] PLUS
the alphabet slice O-8b [H4-M1]".

**The leaf list.** Rows 1–9 = §3.1's table = the D-3 node's list (K-DICT, K-RUN,
K-HALT/ASSEMBLY, drainage, Haar normalization, sibling independence, plus the Dfloor
floor, the CU re-labels, O-1thr, and LIT-4) crossed with the (UB) chain's Step-16
Consumes-list. Row 10 was found mid-audit inside rows 3/6 and ADDED.

---

## 2. The table, row by row

### 2.1 Row 1 — Dfloor D-1/D-2/D-4 (Haar floor, cylinders, ns-null, level-N mass)

**Consumed at:** Step 1 → (UB) via the transported chain.
**Source of the ℚ_p-stated leaf:** `Dfloor_phaseB_verifybrief_rev2.md` (Prop H1,
Lemma H0/H2, SEP, TYPE/PART, MEAS-BRIDGE, BRACKET/SEM-DRAIN/SEM-DRAIN-RATE, SUM-ONE,
Lemma ID, TRANSFER, BASE-0/BASE-1/ADD/LIN, Appendix A Lemma NULL).

**Re-based statement (displayed).**

> **(Dfloor)^δ.** Let G_δ := O_δ^n, C_N(x) := x + (m^N)^n. (D-1^δ) There is exactly
> one translation-invariant Borel probability μ^δ on G_δ; μ^δ(C_N(x)) = q^{−nN} for
> every N, x; for n ≥ 1 singletons are μ^δ-null; μ^δ = (μ^δ₁)^{⊗n}. MEAS-BRIDGE
> (i)–(v) verbatim with p^{nN} ↦ q^{nN} (EXACT in the strict convention);
> BRACKET/SEM-DRAIN/SEM-DRAIN-RATE with the rate read in q. (D-2^δ) Every monic
> separable degree-n f over K_δ has exactly one degree-n splitting type; the
> nonseparable locus is μ^δ-null; Σ_σ α_δ(n, σ) = 1; TRANSFER verbatim (Lemma ID is
> already stated over an arbitrary infinite Z ⊆ ℤ — the source note says so
> explicitly, naming prime powers q = p^δ as the intended instance). (D-4^δ)
> BASE-0/BASE-1/ADD/LIN verbatim; BASE-1(a)–(d) at density 1 = R_{(1,1)}(q).

**Base-touch walk (the delta).** Prop H1's proof template carries verbatim: cylinders
are ultrametric balls (nested-or-disjoint), a level-M class splits into exactly
q^{n(N−M)} level-N classes (coordinatewise: each residue mod p^M has q^{N−M} lifts
mod p^N over O_δ), complement of a class = the other q^{nN} − 1 classes; Carathéodory
+ π–λ + translation-permutation are base-blind. Appendix A (ns-null): Res/disc are
ℤ-coefficient polynomial identities in the coefficients (Sylvester — base-free,
exactly the §3.1 row's "resultant/Vandermonde base-free"), a nonzero one-variable
polynomial has ≤ deg roots in the FIELD K_δ, and Tonelli on μ^δ_{m−1} ⊗ μ^δ₁ closes
the induction. TYPE/PART: unique factorization in K_δ[X] (Euclidean domain — any
field) + LIT-2 defectlessness at its printed scope (complete discrete, char 0 —
contains every K_δ) + e·f additivity. BASE-1's own text already displays the
base-change remark ("uses nothing about ℚ_p beyond completeness of a discretely
valued field with finite residue field … e.g. K_δ = W(𝔽_{p^δ})[1/p]") — walked here,
found exact, including the (f) fence (the algorithmic half stays fenced at the
re-based classifier nodes, rows 2–4).

**Class: (iii) CLOSED.** No new base content; inherited rows: the T-U kernel ledger
conditionality of D-2's general-n instance (unchanged at both bases).

### 2.2 Row 2 — K-DICT (O-2/O-2a dictionary layers not already DVR-stated)

**Consumed at:** Steps 7/10–12.
**Source:** `O2a_phaseB_verifybrief_rev4.md` (+ rev 5 trims per the CU record):
carriers 𝔈 (dressed histories, laws W1–W5), formal codomain 𝔗, Θ total/truncation-
compatible, Cons_f (intrinsic positional clauses), Lemma R; Theorem 1 (order ≤ 1);
Theorem 2(A)–(D) given OL-2a-1..6; the literature layer (L1)–(L9).

**Re-based statement (displayed).**

> **(O-2a)^δ.** The carrier (𝔈, W1–W5, 𝔗, Θ, Cons_f, Lemma R) verbatim, with every
> residue-datum in a record (residual coefficients, tower-field elements, digit
> readings) RECONSTRUCTED over F_δ per the REL.1 rule; Theorem 1 (the order-≤ 1
> engine↔GMN dictionary) over O_δ; Theorem 2(A)–(D) over O_δ, conditional on
> OL-2a-1..6 stated at the re-based carriers; the (L1)–(L9) transcription layer read
> at GMN's printed scope with K := K_δ, F := F_δ, all (e_i, f_i) RELATIVE to K_δ.

**The charged split (DVR-general core vs ℚ_p-worded remainders), executed.**
(a) DVR-GENERAL CORE, class (i): the GD families and the order-≤ 1 engine core — the
ROOT (H1) row's own accounting reads "order ≤ 1 PROVED over an arbitrary complete DVR
for all four faces (leaf #4; O-2a's core; …)", resting on the GD23 generality audit
(V26-confirmed: "no proof uses completeness, perfectness, or a Teichmüller section").
(b) ℚ_p-WORDED REMAINDERS, walked: (b1) the (L1)–(L9) GMN transcriptions — printed at
the paper's standing scope "a fixed finite extension K of ℚ_p" (row 9's evidence
chain), so K_δ is an INSTANCE, with the one delta that residue degrees are relative to
F_δ; (b2) the integer frames / positional clauses ((c0)–(c2), (s_i, u_i)) are
value-group data — unchanged (unramified base, v(p) = 1); (b3) Θ/𝔗 are formal chain
data — class (ii), p-free; (b4) every residue-theoretic OBJECT is rebuilt over F_δ —
that reconstruction (stage laws, digit displays, alphabet products) is (H4a)'s
content, owned by H4-M1/M2 (pointer, not absorption). OL-2a-1..6 are OPEN at base
ℤ_p already and re-state verbatim at the re-based carriers: inherited, named, carried
by the (H1)(b)/(c) rows.

**Class: (iii) CLOSED** (statement shell mechanical; proved core class (i) at its
printed/audited generality; residue-object rebuild → H4-M1; conditionality inherited).

### 2.3 Row 3 — K-RUN (O-3 ⊕ O-2b)

**Consumed at:** Steps 10–12.
**Source:** `O3design_phaseB_attempt.md` (DES-1..7, objects (O1)–(O6), faces F1–F6,
the IND(N) induction on (N, k) lexicographic) + `O3adj_adjudication.md`.

**Re-based statement (displayed).**

> **(O-3 ⊕ O-2b)^δ.** The statement layer DES-1..7 verbatim with the standing
> precondition re-based: f monic degree n over O = O_δ, separable; ns-free carriers;
> the pinned representative family F_rep over F_δ. Realized run set Run_N(x) for
> level-N boxes x ∈ (O_δ/p^N)^n; no-phantom / nothing-missing / nonempty-locus /
> acceptance-exact + OB1/OB2, proved by the same well-founded induction IND(N).

The source note itself anticipated this row: its standing-preconditions line reads
"over O = ℤ_p (D-3 will re-scope to W(F_q) later)". Architecture note: after two
REJECTs the joint-induction design was REPLACED by the K-RUN-C composition
(`O3adj_adjudication.md` §3: no-phantom = O-2a 2(D)/OL-6; no-missing/adequacy/state
binding = CU-1; leaf coverage = O5triple counting; nonemptiness = O-14a′ + D-14;
acceptance = O-1thr Thm 3 + O-2a 2(B) + TB-CAP). The re-based statement below and
the split are indifferent to which architecture is read — every composition piece
is a row of this table — and the carve-out of point (c) SURVIVES the replacement
verbatim: O3adj's CU-3 line names "O-14a′ RunRealizerExists (**ZMod p collapse** +
last-node closure)" as the nonemptiness supply.

**Split, executed.** (a) The induction ARCHITECTURE (well-founded on (N, k), the
displayed intra-level acyclic order) and the statement layer are base-free — class
(ii)/(iii). (b) The engine-seam and dictionary consumptions re-base per row 2 (same
carriers), with OL-2a-1..6 + (LC-COH) + (M6b) inherited. (c) **The carve-out (found
mid-audit → row 10):** object (O4)(i)'s canonical-policy supply is discharged in the
source ONLY at the prime ambient field — verbatim: "dischargeable at F = ZMod p by
O14ap rev-2 Theorem 1 + Corollary 4, the verifier-confirmed prime-field collapse; the
intended instance K = ℚ_p has ambient F = 𝔽_p, so this supply is PROVED for the
cluster's scope" — and the source's §2 conditionality paragraph flags, verbatim: "The
O14ap (S6b′) residue at deg Φ > 1 is NOT inherited at the intended instance
(prime-field collapse covers F = 𝔽_p); **it re-enters only at D-3's unramified
re-scope — flagged for D-3, not here.**" This audit IS D-3's re-scope; the flag lands
as row 10. Face F3′ (nonempty locus) consumes the same O-14a′ realizer theorems
(via CU-3, row 6) — second consumer, same carve-out.

**Class: (iii) CLOSED for the row's own text** — the re-based statement layer and
induction carry mechanically, all inherited rows named — **with the O_δ realizer
supply explicitly NOT closed here: it is row 10's class-(iv) lemma.** (The
completion criterion is computed over all ten rows, so nothing is laundered by the
carve-out.)

### 2.4 Row 4 — K-HALT/ASSEMBLY (O-5/O5triple: leaf labels, Thm E separable-lift scope)

**Consumed at:** Steps 11/12, 17 (D-11 M3 tranche).
**Source:** `O5triple_phaseB_verifybrief_rev3.md` (Theorem A; Theorems B–E at
interfaces (I-1)–(I-3); Lemmas H0/NODE, REP-IRR, STEEP; the three transcription flags
(GMN-COH)/(R-1)/(R-2)/(L3+)_r).

**Re-based statement (displayed).**

> **(O-5)^δ.** (Theorem A^δ, semantic, unconditional over the pinned floor) For every
> monic separable g ∈ O_δ[x], the halted GMN dissection tree 𝒯(g) over K_δ carries a
> factor system whose leaf map is a BIJECTION onto the monic irreducible factors of g
> over K_δ, with product identity, pinned (e, f) invariants per leaf kind — (e, f)
> RELATIVE to K_δ — and checksum Σ e·f = n. (Theorems B–E^δ) The classifier triple
> (LEAF-DISJOINT/COVER/MULT + K-HALT LEAF + ASSEMBLY, type(g) = typemult(T) = σ for
> EVERY monic separable lift of a decided ns-free class in (O_δ/p^N)^n) verbatim from
> the re-based interfaces (I-1)–(I-3) (= rows 2–3's re-based faces). Lemma STEEP's
> corner dichotomy and lift-invariant verdict verbatim.

**Base-touch walk.** Theorem A's tree induction is base-generic given its literature
floor, and the floor's printed scopes all contain K_δ: the GMN pins (Thm 1.15/1.19/
3.1/3.7, Cor 1.20/3.3/3.8, Thm 2.11, Cor 4.19) at the standing scope K/ℚ_p finite
(row 9); HEN-LIFT (LIT-3) at "any Henselian DVR" (coprimality hypothesis, not
tameness); DEFECTLESS (LIT-2) at "complete discrete, char 0". REP-IRR/STEEP are
polygon-and-residual arithmetic over those pins — carries. Thm E's separable-lift
scope: disc is a fixed ℤ-polynomial in the coefficients, so g ≡ g₀ (mod m^N) ⇒
disc g ≡ disc g₀ (mod m^N) — verbatim over O_δ. Per-box lift uniformity (D-15)
re-bases at row 7. The three transcription flags are GMN-internal reading duties —
inherited unchanged (their content is generic in GMN's K).

**Displayed source correction (found mid-audit; a defect in the leaf's own D-3
remark, recorded in-row per the ADD rule's spirit — it names no new leaf).** The
source's hygiene note 3 says "(L1)–(L13) are stated by GMN over an arbitrary complete
discretely valued field". That over-states GMN's printed scope: the 2026-07-03
audit-fix (re-verified 2026-08-01, `docs/GMN_citations.md` §6.0 item 2) pins GMN's
scope as "a fixed finite extension K/ℚ_p" (gmn.txt:381). The correction COSTS NOTHING
here — K_δ is inside the true printed scope — but the O5triple brief's sentence
should be re-worded at its next touch (owed pointer, §4). The same note's second
sentence stands as written: "The LIT-4 audit's 'K = ℚ_p exactly' caveat constrains
the AXIOM DECLARATION, not the mathematics" — see row 9.

**Class: (iii) CLOSED** (inherited: (I-1)–(I-3) point at rows 2–3; the P(O5t) pass).

### 2.5 Row 5 — drainage (O-4/O4T TR-OM; AGR seam = CU-2 + CU-4 + GMN Cor 4.19)

**Consumed at:** Step 13.
**Source:** `O4T_phaseB_verifybrief_rev4.md` (FLOOR, TR-Q, N3-BRACKET, TR-OM;
imports I-TAIL + M05 Lemmas B/D; the (AGR) display and its decomposition).

**Re-based statement (displayed).**

> **(O-4/O4T)^δ.** (FLOOR^δ) c^sem is a well-defined nonincreasing function (separable
> lifts exist over O_δ — M05 Lemma B's template). (I-TAIL^δ)
> μ^δ{ a : v(disc f_a) ≥ m } ≤ (n−1)·q^{−max(0, ⌈(m−w)/(n−1)⌉)}. (TR-Q^δ) a
> nondecreasing unbounded majorant N(f) ≤ Γ(v(disc f)) converts (I-TAIL^δ) into the
> explicit drainage envelope; N3-BRACKET verbatim. (TR-OM^δ) the same conclusions for
> the as-built OM classifier, CONDITIONAL on (AGR)^δ: for every monic separable f of
> degree n over O_δ, the classifier-decided counts agree with the semantic counts
> (O-4's OL1-ii seam), decomposed exactly as CU-2^δ + CU-4^δ + GMN Cor 4.19 at K_δ.

**Base-touch walk.** I-TAIL's proof is discriminant-valuation cylinder counting —
the template carries with p ↦ q (row 1's mass law). M05 Lemma D (Krasner–Hensel local
constancy) is valuation-theoretic over any complete discretely valued field. The
(K)-identity and case arithmetic (the GAP-1-repaired v(α − r) > 0 criterion) are
valuation-geometric — note fractional root-difference valuations occur at BOTH bases;
nothing sharpens or breaks. **The pin check charged by §3.1 ("GMN Cor 4.19's stated
generality checked at the pin, not assumed"), executed:** Cor 4.19 (termination:
for monic separable f there is r ≥ 0 with every type in t_r(f) f-complete, within
ind(f) steps) is pinned at ROOT §4 item 1 under GMN's standing scope sentence — "We
fix a finite extension K of Qp" (LITUNIT §0 sanity anchor, gmn.txt:381; independently
`docs/AXIOM_FAITHFULNESS.md`: AX-GMN-IV audited "within GMN's true scope (a finite
extension of Q_p)" with the arbitrary-DVF over-claim explicitly STRIPPED there) —
and RE-READ AT SOURCE by this unit (row 9's tier-2 glance): Cor 4.19 at gmn.txt:3413
is verbatim "Let f(x) ∈ O[x] be a monic and separable polynomial …" in the generic
O = O_K. K_δ is a finite extension of ℚ_p: the pin covers it as printed; the ind(f)
bound reads verbatim with v normalized on K_δ. (AGR) is OPEN at base ℤ_p and stays the SAME open
seam over O_δ (its eventual proof = the re-based rows 6 + this pin): inherited, named.

**Class: (iii) CLOSED.**

### 2.6 Row 6 — CU cluster (CU-1..CU-4, CU-2t)

**Consumed at:** Steps 10–12.
**Source:** `CU_cluster_phaseB.md` (the consolidated re-label unit; §8 summary; §9
CU-2t executed) + `CU1_phaseB_attempt_rev3.md`.

**Re-based statement (displayed).**

> **(CU)^δ.** The re-label statements verbatim over the re-based carriers of rows
> 2–3: CU-1^δ (the induction; per its rev-2 pins (P-ROOT)/(P-KEY)/(FR≡));
> CU-2^δ (no-phantom) = (O-2a)^δ Thm 2(D) + (A)–(C); CU-2t^δ (terminal seam) — the
> forced terminal datum and record-consistency predicate RC verbatim at re-based
> records, proof route (O-2a)^δ 2(B) + Cor 1.20/3.8 read at K_δ + TB-CAP windows;
> CU-3^δ (nonempty locus, coherent form) = O-14a′^δ + D-14^δ + (O6)^δ;
> CU-4^δ (acceptance, selected-f) — the same assembly walk over CU-1/2/2t^δ + D-15^δ.

**Base-touch walk.** These are re-labels and assembly: their base-dependence is
exactly their proof homes' — rows 2 (O-2a), 7 (D-14/D-15), 9 (the GMN pins Cor
1.20/3.8), plus TB-CAP's windows (valuation-window arithmetic; integer thresholds
unchanged — unramified base). Inherited rows, named: the four owed P(·) passes,
GD-1..6 residue, D-12r (TB-CAP's perimeter), (E-N). **One leg does NOT close
mechanically: CU-3's O-14a′ realizer leg** — the witness construction consumed there
is proved at the prime ambient field only (prime-field collapse); over O_δ, δ > 1 it
is row 10's open lemma. CU-3^δ is therefore displayed as conditional on RRE-δ
(row 10) — the second consumer, after row 3's (O4)(i).

**Class: (iii) CLOSED** (with the row-10 dependence displayed; nothing else new).

### 2.7 Row 7 — O-1thr (D-14/D-15 cylinder laws)

**Consumed at:** Step 18 K4-CYL (and Step 6's deliveries D-14/D-15 → CU/Steps 10–12/17).
**Source:** `O1thr_phaseB_verifybrief_rev4.md` (Theorem 1 = D-14 read locality;
Theorem 2 = O-1(thr); Theorem 3 = D-15 exact cylinder classification; POS/DEV/R-LOC;
the §4 sloped/sheared thresholds β_{i,j}; WGEO/ROOT-M/VAL1/KEY1/DIV1/VTX/SPAN;
(V1)/(V2) key-compliance; (M6a)/(M6b)/(M6c); REAL≡).

**Re-based statement (displayed).**

> **(O-1thr)^δ.** (D-14^δ) Per-site read locality: the re-based machine's read at a
> site depends only on box data below the displayed per-site threshold — thresholds,
> sheared window heights β_{i,j}, bands, and ceilings are the SAME integers/rationals
> (value group ℤ, v(p) = 1: the shear arithmetic is untouched by the base change).
> (Thm 2^δ) the per-site threshold law for compliant policies, same conditional
> structure. (D-15^δ) decided ns-free verdict classes are EXACT finite unions of
> level-t cylinders in (O_δ/p^t)^n — cylinder counts and masses q-powered (row 1).

**Base-touch walk.** The §3.1 expectation "RE-BASE MECHANICAL (valuation-geometric)"
is confirmed for the cylinder/threshold layer: every proof there manipulates
valuations, polygون heights, and window arithmetic in the value group — identical
over O_δ. The graded/residual layer (WGEO's graded cancellation, KEY1's weighted-
Gauss argument, VAL1/DIV1) consumes: MacLane Def 4.1/Thm 4.2 at its printed scope
"any field K, any real non-archimedean value" (LITUNIT: discreteness only in
§§7/8/16) — class (i); and the (V2) block = the GD-3 residual-dictionary MIN CORE,
order ≤ 1 proved over an arbitrary complete DVR (GD23 V26). Residue objects
(ψ̂_hom, in(f), digit readings) are rebuilt over F_δ per REL.1 — the rebuild is
(H4a)/H4-M1 content, pointed. (V1)/(V2) compliance at order ≥ 2 and (E-N) are OPEN
at base ℤ_p — the (H1)(d) row — inherited identically, named.

**Class: (iii) CLOSED.**

### 2.8 Row 8 — O-10 sibling independence (K-COUNT/K-JAC)

**Consumed at:** Step 15 → K1.
**Source:** `O10_phaseB_attempt_rev2.md` (K-COUNT Theorem 1: exact fiber counts;
Theorem 2: adapted-cell O-10 with the D-8 guard; Lemma 3 = K-JAC polydisc form;
K-FACT consumed by citation).

**Re-based statement (displayed).**

> **(O-10)^δ.** For m ≥ 1 monic f₁, …, f_m ∈ O_δ[x], pairwise coprime in K_δ[x],
> ρ_{ij} := v(Res(f_i, f_j)) < ∞, ρ := Σ_{i<j} ρ_{ij}, pinning depth τ ≥ ρ + 1:
> (K-COUNT^δ) the fibers of the level-N multiplication map on factor tuples over a
> ρ-separated polydisc are constant at every N ≥ τ, of size q^{Σᵢ min(eᵢ, N−τ)} for
> the Smith profile (eᵢ) of the Sylvester block map — = q^ρ exactly in the guard
> range N ≥ τ + e_max; (Thm 2^δ) the adapted-cell O-10 statement carrying the D-8
> guard, verbatim; (K-JAC^δ) the Jacobian factor is q^{−ρ} (the §3.1 row's
> "Jacobian p^{−ρ} ↦ q_δ^{−ρ}", exactly).

**Base-touch walk.** The factor-coordinate proofs carry: the Sylvester-block
determinant identity is a ℤ-polynomial identity (base-free); Smith normal form is
available over the DVR O_δ with elementary divisors p^{e_i} (principal ideals are
p-powers — the same profile arithmetic); the counting substrate is
|O_δ/p^k| = q^k, turning every fiber count p^{…} into q^{…} with the SAME exponent
lattice (the exponents are valuation data, unchanged); Newton absorption is
valuation-theoretic; Proposition 1 (coprime factorization rigidity) is Hensel over a
complete DVR. K-FACT stays the recorded GMN citation (row 9's scope chain). The
K-LOC/(I-τ) interfaces stay open exactly as at base ℤ_p — inherited (the (H7) pair),
named.

**Class: (iii) CLOSED.**

### 2.9 Row 9 — LIT-4/(OM-SAT): audited scope "K = ℚ_p exactly"

**Consumed at:** dictionary node O-2 (Steps 11/12 via Cor 1.20/3.8; CU-2t directly).
**Charge (§3.1, verbatim):** "REAL CONTENT, named: re-derive the OM-SAT certificate
over K_δ from the pinned GMN loci at their printed generality, or re-scope; the ROOT
LIT-4 entry itself names this duty as '(UB-X)(a) content'." Expected class (iv).

**The pinned statement.** LIT-4/(OM-SAT): a realized OM branch with residual
multiplicity 1 at its last read certifies an irreducible factor with e = e₁⋯e_r,
f = f₀f₁⋯f_r (GMN Cor 3.8 + Def 3.9; order-1 instance Cor 1.20).

**Re-based statement (displayed).**

> **(OM-SAT)^δ.** Over K = K_δ (residue field F = F_δ): for a type t of order r − 1
> with residue tower F_δ = F₀ ⊆ F₁ ⊆ … ⊆ F_r (each F_{i+1} = F_i[y]/(ψ_i), ψ_i
> irreducible over the RECONSTRUCTED F_i), a root θ of G_i with a_i = 1 gives G_i
> irreducible over K_δ with f(L/K_δ) = f₀f₁⋯f_r and e(L/K_δ) = e₁⋯e_r — all residue
> degrees f_j = deg ψ_j RELATIVE to F_δ (absolute residue degree over ℚ_p = δ·f, the
> base-index convention; e is unaffected — K_δ/ℚ_p unramified).

**The audit (this is the "re-derivation at printed generality" — it is a
SPECIALIZATION, not new mathematics).** The decisive fact: **GMN's standing printed
scope is a FIXED FINITE EXTENSION K of ℚ_p**, NOT ℚ_p itself. Evidence, in two
tiers.

*Tier 1 — the pinned records (independent, with line anchors):*
(a) LITUNIT §0 (2026-07-31): the extraction sanity anchor is the verbatim sentence
"We fix a finite extension K of Qp" at gmn.txt:381;
(b) `docs/GMN_citations.md` §6.0 correction 2 (2026-07-03 audit-fix, re-verified
2026-08-01): "GMN's scope is a fixed finite extension K/ℚ_p (gmn.txt:381), NOT 'an
arbitrary complete DVF'";
(c) `docs/AXIOM_FAITHFULNESS.md` (the AX-GMN audit): "the eight axioms are within
GMN's true scope (a finite extension of Q_p)" — including AX-GMN-III, whose content
IS the Cor 3.8 leaf dichotomy;
(d) the M06 audit note that COINED the caveat says exactly this: "GMN work over K
finite over ℚ_p — **here K = ℚ_p exactly**, so none of the scope over-claims flagged
in AXIOM_FAITHFULNESS are needed" — i.e. "K = ℚ_p exactly" records WHERE THE PROJECT
CONSUMED the pin (so that no widening beyond the printed text was needed), not a
restriction of the printed text.

*Tier 2 — fresh source-glance, RE-PERFORMED BY THIS UNIT* against the surviving
LITUNIT extraction (`/tmp/litunit/gmn.txt` at audit time; same geometry — the anchor
sentence verified at line 381). Verbatim, gmn.txt:381–382 (§1.2 standing setup):
"We fix a finite extension K of Qp as a base field, and we denote v := vK, O := OK,
m := mK, F := FK, **q := |F|**. We fix also a prime element π ∈ O." (GMN itself
carries a general residue-field size q.) The four loci re-read at source:
- **Cor 1.20** (gmn.txt:937): "let θ ∈ Q̄p be a root of Gi(x), and L = K(θ). Then
  f(L/K) is divisible by m deg ψi. … if ai = 1, then Gi(x) is irreducible in O[x],
  and f(L/K) = m deg ψi, e(L/K) = e." — generic (K, O).
- **Cor 3.8** (gmn.txt:2844): same generic phrasing; its proof runs through the
  embedding (36) F_r[y]/(ψ_{r,i}) ↪ F_L, Prop 3.5(4), the Theorem of the product,
  and Cor 3.3 — all in the generic tower over F.
- **Def 3.9** (gmn.txt:2867): generic ("applying Corollary 3.8 in order r − 1").
- **Cor 4.19** (gmn.txt:3413): "Let f(x) ∈ O[x] be monic and separable. There
  exists r ≥ 0 such that all types in tr(f) are f-complete" — generic O.
Re-narrowing hunt: the only "K = Qp" in the body (gmn.txt:1278) is an illustrative
example ("For instance, for K = Qp, π = p, …"), not a scope change; the base-field
manipulations at gmn.txt:879/2759 are unramified base WIDENINGS inside proofs.

Every K_δ = W(F_{p^δ})[1/p] is a finite (unramified) extension of ℚ_p, hence an
instance of GMN's printed K (with π = p). The statements are phrased entirely in
(K, O, m, F, F_i, e_i, f_i, v, q) with no ℚ_p-specific ingredient; the symbol walk
under K := K_δ is displayed above (F := F_δ, q := p^δ; v(K_δ^×) = ℤ with v(p) = 1;
(e, f) relative). The consumption discipline is PRESERVED, not widened: (OM-SAT)^δ
is consumed only through the re-based dictionary node O-2 (row 2) — no axiom typed
at corpus carriers (the V4/M15 trap), same as at δ = 1.

**Class: (i) CLOSED — stated-general already at the needed generality** (the needed
targets are exactly the K_δ, all inside the printed scope; note class (i) is claimed
at {K/ℚ_p finite} ⊇ {K_δ}, NOT at arbitrary DVRs — GMN does not print that, per the
§6.0 correction). **Displayed residue, MECH (not mathematics):** (1) the ROOT §4
item-1 roster line and the tree's LIT-4 entry still carry "audited scope K = ℚ_p
exactly" with the K_δ duty pointed at (UB-X)(a); with this row executed, the caveat
should be re-worded to "printed scope K/ℚ_p finite; consumed at K = ℚ_p and — per
H4M3 row 9 — at K = K_δ" (ROOT-owner sync, rides H4-M7); (2) the standing
printed-TAMS pagination confirmation (LITERATURE-CONDITIONAL, already owed for every
GMN pin) covers these loci too — nothing new is owed by this row. Honesty note: the
closure rests on the tier-1 pinned records AND the tier-2 source-glance re-performed
by this unit at the arXiv-v2 extraction (the anticipated demotion contingency —
"what if a fresh source-glance is required?" — was thereby discharged in-unit; only
the printed-TAMS pagination flag, standing for every GMN pin, remains). Robustness:
even if the hostile pass faults this row's closure, the (a)-verdict of §3 is
UNCHANGED (row 10 already holds (a) open).

### 2.10 Row 10 (ADDED) — the O-14a′ run-realizer supply (RRE) at ambient F = F_{p^δ}

**Found mid-audit** inside rows 3 (object (O4)(i)) and 6 (CU-3's witness leg); ADDED
as its own row per the standing rule. **Consumed at:** Steps 10–12 through O-3's
canonical-policy pin and CU-3's nonempty-locus witness construction.
**Source:** `O14ap_phaseB_attempt_rev3.md` + `O14ap_phaseB_verifybrief_rev3.md`.

**The ℚ_p-stated facts on file (twice-verified, rev 3 rescope):**
- RRE(p, F) := every coherent history whose final node is a recentering admits a
  center realizer t with (CR1) ∧ (CR2) ∧ (CR3) (interior recentering nodes are
  immediate from the node's own record, (r4)–(r6) — base-free).
- **Theorem 1 (prime-field collapse):** at F = 𝔽_p every coherent history has all
  ν.g = 1 and all frame keys linear, so (CR2) is FREE; with Theorem 3 (last-node
  flank, from coherence alone — field-generic) this gives `RRE(p, ZMod p)` — PROVED,
  and FORMALIZED Lean-core (`MovesD/R7_runRealizer.lean`, `runRealizerExists_zmod`).
- **REFUTATION (general F):** the compiled singleton-support clause (CR2) is
  REFUTED-AS-STATED at deg Φ > 1 — the F₉ inert-quadratic countermodel. F₉ = F_{3²}:
  this is EXACTLY a (p, δ) = (3, 2) instance of the re-based engine's ambient field.
  So the mechanical re-base of the consumed statement is FALSE — this row cannot be
  class (iii).
- The corrected support law is **Conjecture 5.4.C** (the stretch-threaded
  (S6b′-SUPP-2) law on class (U)), DEMOTED from a theorem after two churn rounds;
  proved fragments on file (Lemma 5.4.0, (THR), Props 5.4.2/5.4.3-conditional/5.4.4);
  two named open lemmas (OL-1 read-level indexing, OL-2 base normalization
  (F0-a)/(F0-b)); a falsifier suite attached at the O14ap unit.
- O14ap's own consumption audit: Conjecture 5.4.C "is consumed by NOTHING on the
  mandatory path" — because "every mandatory-path consumer [is] run at the prime
  ambient field". Over O_δ with δ > 1 that escape clause is exactly what expires.

**Re-based statement — the named class-(iv) lemma (displayed, OPEN):**

> **LEMMA RRE-δ (OPEN).** For every δ ≥ 1, over the re-based engine at base O_δ
> (ambient residue field F_δ = F_{p^δ}): every coherent history whose final node is a
> recentering admits a center realizer satisfying (CR1) ∧ (CR2^δ) ∧ (CR3), where
> (CR2^δ) is a FAITHFUL general-F support law (the corrected (S6b′-SUPP-2) form on
> class (U) — O14ap Conjecture 5.4.C's perimeter — or a re-adjudicated equivalent);
> equivalently, the supply that discharges the re-based (O4)(i) canonical-policy pin
> and CU-3^δ's witness construction. Instances: δ = 1 is PROVED and machine-checked
> (`runRealizerExists_zmod`; (CR2) free by Theorem 1(iii)). δ > 1 is OPEN: (CR1)+(CR3)
> exist from coherence alone (Theorem 3, field-generic), the compiled (CR2) is FALSE
> (F₉ countermodel), and the corrected law is Conjecture 5.4.C — unproven.

**Two discharge routes, priced (neither executed here — the row stays (iv)-OPEN):**
(A) PROVE Conjecture 5.4.C (+ its OL-1/OL-2) at class (U) and re-run the O14ap
DELTA-1 consumption audit over O_δ — mathematics, owner naturally the O14ap orbit /
a dedicated H4 follow-up unit; or (B) RE-SCOPE the re-based consumers: adjudicate
whether the O_δ-side (O4)(i) pin and CU-3^δ can consume a (CR1)+(CR3)-only realizer
(dropping the (CR2)-shaped clause), which is a STATEMENT-PRECISION step on O-3/CU-3's
ledger rows — a ROOT/O-3-owner move requiring its own sign-off, not performable
inside this audit. Route (B), if it lands, would retire this row without new
mathematics; until one route lands, the row is the displayed residue of (UB-X)(a).

**Class: (iv) — REAL CONTENT; Lemma RRE-δ OPEN.**

---

## 3. Completion-criterion adjudication (the finding-9 gate, executed)

Criterion, verbatim from the unit spec: "(a) counts DISCHARGED only when every row is
class (i)–(iii) CLOSED or its class-(iv) lemma is PROVED; an open named lemma … leaves
(a) OPEN with that lemma as its displayed residue, and H4-M6/M7 stay BLOCKED on it."

- Rows 1–8: class (iii) CLOSED (row 2 with a class-(i) core; rows 3/6 with their
  realizer legs carved out to row 10, displayed).
- Row 9: class (i) CLOSED (MECH sync residue only; robustness note in-row).
- Row 10: class (iv), **Lemma RRE-δ NOT proved.**

**Therefore (UB-X)(a) is OPEN. Displayed residue: Lemma RRE-δ (§2.10). H4-M6 and
H4-M7 remain BLOCKED on it.** The §3.1 row's "honest expectation: LIT-4 is class
(iv)" is REFUTED by the executed audit — the residue is not the literature scope
(which the printed text already covers) but the run-realizer seam, pre-flagged for
D-3 by O3design and landed here. Note for wave-planning: Lemma RRE-δ is INDEPENDENT
of (H4a)/(R1)–(R4) (it lives at the engine's coherence/realizer layer, not the
stage-tower laws), so H4-M1/M2's landing does not discharge it; conversely proving
RRE-δ does not touch (H4a). A dedicated unit (or the route-(B) adjudication) is
required.

## 4. Owed pointers (recorded, not self-served)

1. **ROOT owner (rides H4-M7):** §4 item-1 roster line + tree LIT-4 entry — retire
   the "K = ℚ_p exactly" caveat per row 9's disposition; sync Step 16's (a)-clause
   display to name Lemma RRE-δ as (a)'s residue.
2. **O5triple owner:** brief hygiene note 3 — one-line correction of the GMN scope
   wording ("arbitrary complete discretely valued field" → "a fixed finite extension
   K/ℚ_p", per `docs/GMN_citations.md` §6.0(2)); no downstream change.
3. **O3design owner:** the §2 D-3 flag ("re-enters only at D-3's unramified
   re-scope") is now LANDED — its landing site is this note's row 10; the O-3 ledger
   may cite Lemma RRE-δ by name.
4. **O14ap owner:** Conjecture 5.4.C acquires its first named forward consumer
   (Lemma RRE-δ, δ > 1); the existing falsifier suite and OL-1/OL-2 become
   RRE-δ-relevant; no text change owed until a discharge route is picked.
5. **Tree owner:** D-3 node — this audit is the "per-leaf scope hygiene" half of the
   D-3 collapse, executed; the node's status line can point here + at H4-M1 (the
   O-8b slice) for the remaining half.

## 5. Hostile-pass record (gate: ×1)

- Pass 1 (Codex, fresh context, self-contained ~88 KB prompt: this note + verbatim
  appendices — blueprint §3.1/finding 9, D-3 node, Step 16, O3design (O4)+flag,
  O14ap rev-3 verdict + §2, gmn.txt scope/Cor 1.20/Cor 3.8/Def 3.9/Cor 4.19
  extracts, GMN_citations §6.0, M06 scope note, O5triple note 3, Dfloor H1/ID/
  BASE-1/NULL, O10 §0–1, CU §8, O4T I-TAIL/(AGR), tree LIT-4 + (H1) roster line).
  Charge: quote-and-classify, fix nothing; priority attack targets = row 9's (i)
  call, rows 3/6's carve-out structure, row 10's lemma statement vs consumer need,
  absorbed-row hunt, per-row delta sufficiency, quote fidelity.
  **LAUNCHED 2026-08-08** (`nohup codex exec --sandbox read-only`, prompt
  `/tmp/h4m3_prompt.txt`, output `/tmp/h4m3_codex_out.txt`); the verdict had not
  returned when this unit's report deadline fired. **STATUS: IN FLIGHT — the gate
  is NOT yet satisfied.** This unit therefore reports PARTIAL (audit executed;
  pass owed), NOT closed-at-gate. Whoever folds the verdict: append the finding →
  disposition table here; a REJECT on row 9 demotes it per its in-row robustness
  note (the §0/§3 (a)-OPEN verdict survives ANY single-row demotion — row 10
  already holds (a) open); a REJECT on row 10's statement re-points Lemma RRE-δ,
  not the (a)-OPEN verdict, unless the verifier exhibits that NO re-based consumer
  needs any (CR2)-shaped clause (route (B) executed — which is a ROOT/O-3-owner
  statement action in any case).
