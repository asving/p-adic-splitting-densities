# SYNTHESIS PASS 4 (SYNTH4) — merged open-lemma families, the O3design adjudication, the recut mandatory path, and the unlocked Lean units

Date: 2026-08-01 (late). Standing duty: hunt big unifying ideas that CUT DOWN the proof.
Sources consumed in full: `docs/MATH_COMPLETION_TREE_2026-08-01.md` + DELTA 1; the
2026-08-01 sections of `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (V9–V25 arcs,
wave 3/4, the Asvin proof-scaffold authority); the Phase-B briefs' honest-residue/
open-lemma sections — `openmath/O12_phaseB_verifybrief_rev4.md` (§1 scope + OL-O12-2),
`O13_phaseB_verifybrief_rev2.md` (§5 (COMP) chain), `O1thr_phaseB_verifybrief_rev3.md`
(§§2.4–2.5, §8), `O2a_phaseB_verifybrief_rev4.md` (§4, the six OLs), `O5triple_
phaseB_verifybrief_rev2.md` (§2 flag roster, §5 interface, §8), `Dfloor_phaseB_
verifybrief_rev2.md` (§8), `O14ap_phaseB_verifybrief_rev3.md` (rescope), `O3design_
phaseB_verifybrief_rev2.md` (full); both REJECT reports V16/V21 (full text) and the
V22–V25 verdicts. Everything below is synthesis and proposal — **the orchestrator
adjudicates**; no tree text, brief text, or Lean file is edited by this pass.

---

## §0 Headline findings (the cuts, ranked by size)

1. **The ~22 named open items across the seven active packages merge into EIGHT lemma
   families** (§1, table). The GMN-dictionary/engine-read seam is ONE subject stated in
   FIVE vocabularies: O-2a's OL-2/OL-3, O-1thr's (V1)/(V2), O5triple's (I-1)(a) legs,
   O3design's JC-2/JC-3, and O-9's OL-B. Two of the mappings are VERBATIM
   (GD-3's minimal core IS (V2c); OL-3 ≡ O-9 OL-B is declared in O-2a's own text).
2. **O-2b has no mandatory-path consumer.** By O3design's own §4 right-sizing table,
   F6′/TT-DET′/MF-MATCH (= K-DICT-OB1) are consumed ONLY by D-16 — which DELTA §D1.4
   struck from the root-mandatory set (rates only). Consequence: **evict O-2b from the
   joint cluster**; the induction becomes O-3-only. This deletes the design's
   self-declared riskiest face (TT-DET′ level preservation) and the D-16-shaped half of
   both REJECTs from the mandatory path — and with it the ENTIRE LIT-5/BNS transcription
   duty (numbering-shift hazards included), subject to one audit (§2.4: OB2's alleged
   D-11 consumption).
3. **The cylinder law should be embraced, not quarantined.** V21 findings 1/2 prove the
   "selected-f" typing is impossible in principle: Run_N(x) depends only on the box, so
   any faithfulness claim universally quantified over separable lifts IS a cylinder law.
   Recut the cluster's target as the box-wise theorem (§2.2) — then D-15 (CYL) is an
   OUTPUT of the cluster, not a separate downstream node.
4. **No-missing (F2′) is mostly already carried.** O5triple's verified sharpening makes
   D-7b coverage counting-only (no no-missing consumed); and the remaining no-missing
   need (F4-C/OL1-ii drainage) reduces to O-1thr's PROVED harvest totality (M6a) +
   no-phantom (M6c)(ii) + the GD dictionary, by induction. F2′ becomes a corollary
   shape, not an independent face (§2.3).
5. **Honest recount** (§3): after this week's landings the mandatory-path open
   mathematics is (i) the GD seam beyond degree-1 first transitions, (ii) flow
   coherence/adequacy (GD-7) + the exact-key seam (GD-8), (iii) engine bookkeeping
   (GD-4/GD-6 incl. the V24 REAL≡ circularity repair), (iv) cluster assembly (F4-C,
   F3′-coherent, box-wise K-RUN), (v) O-9's OL-A/C/D + O-10's K-COUNT/K-JAC, (vi) the
   instance pin (D-11 + OL-O12-2) + O-11 assembly, (vii) D-3 as scope hygiene +
   O-8b's (R1)–(R4), plus literature pulls and the verification-only queue. Items
   (i)–(iii) are ONE mathematical subject — a single dedicated GD campaign is the
   shortest path (§3.3).
6. **Four Lean units are unlocked now** (§4): the O-12 pole-free theorem (VERIFIED),
   the Dfloor measure floor (pass-1 clean; = Asvin's target capstone shape), O5triple's
   abstract counting lemma (unconditional), and the WGEO/VTX degree-1 perimeter (which
   retires Lean interface rows (M6b)(i)/(N4)-upper and aligns with HK-11a/HK52). Plus
   the highest-leverage consolidation: ONE `GDInterface` hypothesis structure replacing
   the scattered (M6b)/OL-2a-*/(I-1)–(I-3) rows.

---

## §1 The merged open-lemma table (families GD-1..GD-8 + the non-merging remainder)

Vocabulary: "↔" = statement-level mapping (each side's exact label quoted from its
brief); "⊂" = one side is the other's special case or minimal core. Status lines name
partials that are PROVED somewhere (with scope) — a partial proved in one vocabulary
transports to all carriers of the family ONLY after the (S-1)-style machine
transcription audit (O-1thr §8), which is itself part of the family's closure.

### GD-1 — representative shape / lift admissibility

**Merged statement.** For every chain/type t of order i and the canonical policy-pinned
key lift Φ_{i+1} = Lift_i(c): (a) Φ_{i+1} is monic in O[x] of degree
m_{i+1} = m_i·e_i·f_i; (b) Φ_{i+1} is a GMN Def-2.12 representative of t —
equivalently, N_j(Φ_{i+1}) is one-sided of slope λ_j with R_j(Φ_{i+1}) ∼ ψ_j at every
j ≤ i, top multiplicity 1; (c) v_{i+1}(Φ_{i+1}) obeys the V-recursion
V_{i+1} = e_i f_i(e_i V_i + h_i). Graded corollary: in(Φ_{i+1}) ∈ gr(w_{i+1}) is, up to
a unit monomial, irreducible homogeneous of Φ_i-degree e_i·g_i, and does not divide
nonzero homogeneous elements of smaller Φ_i-degree. Quantifier: cumulative/joint strong
induction on order (O-2a rev-4 P2-4 reading).

| carrier | exact label | relation |
|---|---|---|
| O-2a §4 | **OL-1 (a)(b)(c)** (pinned Lift form) | = the merged statement |
| O5triple §2 | **(R-1)** "the constructed φ_r has one-sided N_i(φ_r) of slope λ_i with R_i(φ_r) ∼ ψ_i at every i ≤ r−1, top multiplicity 1" | = clause (b) at GMN's constructed representative; V23 gap 3 correctly reclassifies it substantive — i.e., (R-1) IS GD-1(b), not a lookup |
| O-1thr §2.5 | **(V2)(a)** key initial form | = the graded corollary |
| O3design §5 | **JC-1** (= OL-2a-1) | = the merged statement |

Partials: GMN Thm 2.11 (existence of SOME representative — the open content is the
pinned one); O-1thr **Lemma KEY1** proves the graded corollary OUTRIGHT at degree-1
first transitions (irreducibility of ψ_hom, degree block, ord computation).
Literature: GMN Def 2.12 / Thm 2.11 (+ the §2.1 chain display, the (R-1) duty).

### GD-2 — frame/valuation tie + development identity (the seam's spine)

**Merged statement.** At every order: (a) the engine stage valuation is GMN's:
u_{i+1} = v_{i+1} on {B ≠ 0 : deg B < m_{i+1}} (engine ℤ-normalization), and w_{i+1} is
multiplicative ((V1), MacLane); (b) the Φ_{i+1}-development computes it from below:
w_{i+1}(B) = min_k (w_{i+1}(C_k) + k·γ̂_i) over the sheared slot heights; (c) hence the
stage window polygon = N_{i+1}(f) vertex-for-vertex, and the emitted record
(e, h, ℓ, s, u) is verbatim (c1) — GMN's side data in the order-(i+1) integer frame.

| carrier | exact label | relation |
|---|---|---|
| O-2a §4 | **OL-2 (a)+(b)** ⇒ **OL-2-min [(c′)+(d′)]** | (a)(b) = merged (a)(c); OL-2-min = the emitted-record consequence (Theorem 2(D)'s only need) |
| O-1thr §2.5 | **(V1)** + **(V2)(b)** "w_{i+1}(B) = min_k (w_{i+1}(C_k) + k·γ̂_i)" | (V1) = multiplicativity; (V2b) = merged (b) verbatim |
| O-1thr §2.5 | **Corollary VTX**'s general-order residue: "the same chain needs e_i·w_i(C_μ) ≤ w_{i+1}(C_μ), i.e. … the development identity (V2b) at level i" | the (M6b)(i)/(N4)-upper discharge consumes exactly merged (b) |
| O3design §5 | **JC-2** (targets the full OL-2 (a)–(d)) + the verbatim (M6b) corollary clause | = the merged statement + its locality corollary |
| O5triple §5 | **(I-1)(a)** side-data leg "through OL-2a-2's frame/side dictionary" | consumption pointer to this family |

Note on axioms-vs-claims: O-2a's stage interface carries (S-K1)
"u(f) = min_j (u(B_j) + j·u(Φ̂))" as an ENGINE AXIOM; (V2b) is the SEMANTIC claim.
GD-2 is precisely the tie: the engine's axiom holds AT the GMN valuation. The compiled
HK52 stretch countermodel (factor-e′ vertex stretch at e′ ≥ 2) lives in clause (c) and
is why OL-2(b) is typed at the EMITTED record — the merged statement keeps that typing.
Partials: **Lemmas VAL1 + DIV1** (O-1thr rev 3) prove (a)+(b) OUTRIGHT at degree-1
first transitions; **WGEO(a)–(d)** derive the window geometry from (V1)/(V2) at every
order; T-F machine check 41,720 instances 0 violations (and 7,472 violations of the
UNsheared reading — the convention pin is load-bearing). V24 repair item inside this
family: DIV1's division argument is written for Φ_0 = X, must cover the general
degree-one lift Φ_0 = X − a. Literature: MacLane Trans. AMS 40 (1936) for (V1);
GMN §§1–2 for (b)/(c).

### GD-3 — residual dictionary / twisted residues

**Merged statement.** At every order, with ψ̂_hom = in(Φ) up to unit monomial:
(min core) ord_{ψ̂_hom}(in(f)) = ord_ψ(R_λ(f)) — the residual polynomial computes
ψ-order of the initial form; (full form) the anchor-normalized engine residual
satisfies R^nrm = c·R_λ(f) for some c ∈ F^× — the z-power twists of GMN Def 2.20's
coefficients are absorbed EXACTLY by the single anchor-unit division of F.2; slot-wise
each residual coefficient read is a bijection of the residue field (no un-cancelled
z ↦ z^a, a ≥ 2).

| carrier | exact label | relation |
|---|---|---|
| O-2a §4 | **OL-3** "R^nrm = c·R_{λ_{i+1}}(f) … hence equal monic-irreducible factor multisets" | = the full form; V25's minimality gap: Theorem 2(D) consumes only the selected factor's (c2) multiplicity — i.e., 2(D) needs only the MIN CORE |
| O-1thr §2.5 | **(V2)(c)** "ord_{ψ̂_hom}(in(f)) = ord_{ψ_i}(R_i(f))" | = the min core VERBATIM |
| O-9 (M08) | **OL-B** "residual coefficients are twisted residues: per-slot a bijection …, no un-cancelled z ↦ z^a" | = the slot-wise clause; O-2a's own text: "Shared with the O-9 leaf's twisted-residue lemma: one proof should serve both" |
| O3design §5 | **JC-3** (= OL-2a-3) | = the full form |
| O5triple §5 | **(I-1)(a)** residual leg "through OL-2a-3's residual identification" | consumption pointer |

Consumption split to record at merge: the CLUSTER needs the min core; the VALUE side
(O-9's census formula → O-11's tables) needs the full form. Partials: KEY1's ord
computation (degree-1 first transitions); M08 Theorem 2 = the level-1 census PROVED
(46-strata machine check); B-4/M6 empirical through OM order 4. Literature: GMN
Defs 2.19–2.21.

### GD-4 — emission/record discipline (engine bookkeeping, not GMN mathematics)

**Merged statement.** Every complete engine run on monic f (disc f ≠ 0) emits a
well-formed dressed history: W1–W5 (only-last-terminal, interior μ ≥ 2, a₀ ≥ 2 at
k ≥ 1, inc ⇔ e·g ≥ 2), fields in declared domains, dressing normalized, level-0
(c0) = ord_{ψ̂₀}(f̄); and every harvested record satisfies the lawfulness laws
(AUX; plus the lower (N4) band).

| carrier | exact label | relation |
|---|---|---|
| O-2a §4 | **OL-4** (emission discipline) | = the run-side half |
| O-1thr §2.4 | **(M6b)(iii)** AUX-at-harvest + **(M6b)(ii−)** lower band | = the harvest-side half (the band consumed only in REAL≡'s lawfulness step) |
| O3design | **JC-4** (OL-2a-4 + K-OB-E) + the OL-2a-4 W-law gate | same family + the μ ≥ 2 semantic sibling |

Proof route on record (both briefs): by construction of the control flow ((τ-irr)
halts at multiplicity 1 ⇒ continuation implies μ ≥ 2, etc.). K-OB-E (continuing ⇒
repeated residual, GMN Def 3.9 arithmetic) is this family's one semantic clause.

### GD-5 — base-read conformance (order 1) — NEARLY CLOSED BY COMPOSITION

**Merged statement.** O-2a's OL-5 (b′)+(c′): the engine's base read emits verbatim
(c1)/(c2) at i = 1. **Mapping that closes it:** O-1thr rev 3 PROVES (V1)/(V2) outright
at root states and degree-1 first transitions (VAL1/KEY1/DIV1 + ROOT-M + WGEO), and
O-2a's (D3) is PROVED ("the displayed formulas ARE (L2)/(L3)'s order-1 objects").
OL-5's own intended proof route is exactly this composition. Residue: ONE transcription
audit — O-1thr's machine ((R1)–(R5) reads, §1.3) vs O-2a's stage interface (F.0–F.2)
clause-by-clause at order 1 (the S-1 seam; both briefs flag it). **Proposal: a
one-page composition note closes GD-5; no new mathematics expected.** Degree-g > 1
root keys (f₀ > 1 tracks) need the KEY1 generalization — small, same method (the
weighted-Gauss ring becomes F_{p^g}[x̄, p̄] via the unramified track extension).

### GD-6 — run decomposition / execution ≡ realization

**Merged statement.** (a) A complete run decomposes into successive stage reads whose
chain parameter is the emitted prefix's formal chain c = Θ(𝐇_{≤i}) — O-2a **OL-6**
(V25: NO critical; the binding is coherent, base and step). (b) Machine execution
coincides with the REALIZED predicate — O-1thr **Lemma REAL≡**, currently holed by the
V24 CRITICAL: (M6c)(ii) is quantified at "REALIZED NON-HALTED" states and then used to
prove the prefix is non-ns-halted — circular. (c) O3design's F1′ conformance warrant
("a working-level-N run reads only digits below N: OL-2a-4 emission discipline + L12
window bookkeeping") is this family's level-accounting clause.

Repair note for (b), suggested shape: prove non-ns-halt DIRECTLY — a realized
continuing child's side is a face of the state's window hull by WGEO(c) alone (which
needs only that the STATE is realized, not the non-halt guard); then (M6c)(ii)
restated with the guard split: at a realized state, EITHER a principal window face
exists (⇒ non-ns-halt, and the child classification proceeds) OR the state ns-halts
and has no realized children (which is the (F5)-clause content). The circle is a
statement-order defect, not (on present evidence) a mathematical one — T-F's 41,720
instances checked exactly the claimed geometry. Owner: O-1thr rev 4.

### GD-7 — flow coherence / process matching / adequacy (the recursion identity)

**Merged statement.** The GMN flow recursion is coherent node-by-node: (a) for a
sprouted type t′ = (t; λ_S, ψ) (a(S,ψ) ≥ 2), the (L9) dissection factor G_{S,ψ}
EQUALS the type-t′ cluster f_{t′}, and ω_{r+1}(f) at t′ = a(S,ψ); (b) the types the
flow sprouts lie in GMN's t_r(f), so Thm 4.18/Cor 4.19 (index charge, termination)
apply to the flow's tree; (c) order-0 anchor: f_{t₀} = g_j with ω₁ = a_j; (d)
consequently every t_•(f) node is reachable by read-back — a Cons_f-history exists per
node (ADEQ surjectivity), conditional on GD-1.

| carrier | exact label | relation |
|---|---|---|
| O5triple §2 | **(GMN-COH)** [M] | = clause (a) verbatim |
| O5triple §2 | **(R-3)** [M] (process matching / (L13) applicability) | = clause (b) |
| O5triple §2 | **(R-0)** [S] (order-0 cluster identification) | = clause (c); V23 gap 2: the product-closure half is substantive — include it in the lemma, not the lookup |
| O3design §2 | **(ADEQ)** leg (ii) read-back surjectivity | = clause (d) |
| O3design §2 | **MF-MATCH** (recentering runs ↔ Montes refinement iterations) | the D-16-only sibling — NOT mandatory (see §2.1); keep in the family for provenance |
| O-4 (M05/V2) | V2 item 4's caveat "≤ ind(f) nontrivial steps needs the charging argument" | = clause (b) consumed at OL1-i |

One GMN reading session (§3.3) covers (a)–(c) + the (R-1) lookup + the L5b
normalization pin + the printed-TAMS pagination confirmation — the whole
literature-facing surface of GD-1/GD-7/GD-8 in one unit.

### GD-8 — exact-key polygon seam

**Merged statement.** (R-2)/(L3+)_r: at ord_{φ_r}(g) = j₀ ≥ 1 the φ_r-development has
the slope-−∞ side of length j₀ contributing the EXACT factor φ_r^{j₀}, finite sides
carrying total length ω − j₀, with the degree bookkeeping. Carriers: O5triple
**(R-2)** [M] (NODE(ii), Thm A(3)); O-2a's order-1 **(L3+)** (falsifier-covered: 871
forced exact-divisibility samples, 0 findings). Self-contained polygon lemma; the
order-1 proof should generalize verbatim over GD-2's frame tie.

### The non-merging remainder (genuinely separate open items)

* **O-10:** K-COUNT (constant-fiber multiplication map, Sylvester/Smith + Newton
  absorption, N ≥ thr + 2ρ) and K-JAC (cell-constant ρ) — the hardest genuinely-new
  quantitative lemmas; D-8 guard + consumer audit ride along. Independent of GD.
* **O-9:** OL-A (order-r slot/level ledger) + OL-C (census formula given OL-A/B; shape
  verbatim level-1) + OL-D (window counts at build time). OL-B is GD-3.
* **Instance pin:** D-11 (MASS-ID) + **OL-O12-2** (complete degree-3 table = an (O3)
  member of 𝔅₃) + contingent OL-O12-1 (fires only if a future pack departs 𝔅_n's
  organizations). O-12 itself is VERIFIED at the honest scope.
* **D-3 / O-8b:** the unramified re-base — (R1)–(R4) (T-1 stage laws over
  O_δ = W(F_{p^δ})); adjudicate the arbitrary-DVR statement discipline at GD dispatch
  (§3.2 step 9) so D-3 collapses to scope hygiene.
* **(E-N)** (O-1thr Thm 3(c)'s count caveat) — open, scoped, NOT consumed by the
  mandatory path (mass/cylinder clauses suffice; rates route only).
* **O-14 residue:** Conjecture 5.4.C (+ its OL-1/OL-2) — consumed by NOTHING on the
  mandatory path (rescope executed; DELTA-1 O-14a′ obligation MET). O-14a/b/c as before.
* **Dfloor conventions:** (C2)'s (τ-irr)/(τ-hen) at degree > 1 = O-5's clauses (owned
  by O5triple's Theorem C, conditional on the cluster interface).
* **K-OB-C (Okutsu proximity):** struck from the mandatory path — O3design's intra-step
  order warrants no-phantom through the dictionary (F1′ ← F5 + OL-2a-2(c,d)/3), and
  O5triple §7 remark 6 explicitly bypasses the Krasner route for D-7a. Only consumer
  left: O-7 (route R-QNT). Pull the citation only if the rates route is elected.

**Count: 22 named open items → 8 families + 7 independent items**, of which the
mandatory path needs the 8 families minus MF-MATCH, plus O-9/O-10/instance-pin/D-3
from the remainder.

---

## §2 The O3design double-REJECT, adjudicated: restructure, don't replace

**The charge answered first.** The repair agent must judge: is the design approach
itself wrong, or is this reviewer severity? Reading V16 and V21 side by side: V16's
five criticals were over-strength and well-posedness (all repaired at rev 2 — V21
finding 4 and the SEM-LAWFUL/CEIL-UB judgments CONFIRM the repairs); V21's blockers
are of a different kind — findings 1/2 are a STRUCTURAL IMPOSSIBILITY (no rev can fix
them by wording), findings 3/5/6 are scoping/ordering. So: **neither reviewer severity
nor a wrong proof idea — a wrong CLUSTER BOUNDARY and a wrong FACE TYPING.** The
induction mechanism itself (well-founded on (N, k), mutual faces, O-2a Thm 1 base) was
confirmed acyclic by V16 finding 6 and never charged by V21. Verdict: RESTRUCTURE along
four moves, each of which the verified pieces already suggest.

### 2.1 Move 1 — evict O-2b from the cluster (the biggest cut)

O3design's own §4 consumer table assigns F6′ (pooled filtered trace correspondence =
OB1) to exactly ONE consumer: D-16 (δ-execution transport). DELTA §D1.4 struck D-16
and all rates from the root-mandatory set. Nothing else consumes OB1: O-5/D-7 need
F4-S + saturation; O-4 OL1-ii needs F1′ + F4-C + Cor 4.19; D-15 needs D-14 + O-1thr
(K2) + F1′/F2′; K-14 needs F1′/F2′/F3′/F5. The tree's original reason for joining
O-2b to O-3 ("needed to consume any BNS iteration/precision bound", O-2 clause (v))
is a rates-only reason. Consequences:
* TT-DET′ (the design's declared riskiest claim), MF-MATCH, P_N quotient
  well-definedness (V21 finding 4's obligations), and gate G-F6′ leave the mandatory
  path — they file under D-16/route R-QNT.
* **LIT-5 (BNS) exits the mandatory path entirely** — Thm 3.13 was already unconsumed;
  with OB1 gone, the BNS §2/§4 transcription duties (and their documented numbering
  hazards) are R-QNT items.
* AUDIT OWED (the one check before executing): O3design's table row "D-11: σ
  invariance | OB2". If D-11's eventual statement really consumes OB2 (σ invariance
  under ∼_OM), the cheap level-free OB2 stays mandatory WITH its BNS §2 pin; if (as
  the tree's D-11 statement suggests — kernel entries as Haar volumes, no ∼_OM
  quantifier) it does not, OB2 leaves too. Flag to the D-11 owner.

### 2.2 Move 2 — type the faces box-wise; D-15 becomes an output

V21 findings 1/2: Run_N(x) is a function of the box alone, so "F1′ for the selected
f" instantiated at two lifts of one box already yields the cylinder law; the D-15
quarantine "fails" — i.e., IS the theorem. Stop fighting it. The recut target:

> **(K-RUN-BOX).** For every level N and residue box x, and EVERY monic separable
> lift f of x: Run_N(x) = {𝐇 ∈ T_can(f) : N*(𝐇) ≤ N}, with acceptance: Cert accepts
> (x, 𝐇) iff 𝐇 is verdict-carrying and N ≥ N*(𝐇) (soundness at every N,
> completeness at the decision level).

One theorem; the lift-uniformity of the right-hand side across lifts of x is a
COROLLARY (both sides equal Run_N(x)), which is exactly D-15's content once combined
with O-1thr Theorem 3's cylinder exactness. This simultaneously: kills the V21-1/2
class permanently (the quantifier is honest); makes G-LIFT a real gate for the stated
claim (V21 finding 6's complaint dissolves); and merges D-15 into the cluster's
deliverables instead of a separate node with its own seam. The nonseparable-lift
corner is handled once, globally: O5triple §7 remark 2 (disc g ≡ disc g₀ mod p^N —
one separable lift with v_p(disc) < N makes all lifts separable) plus the ns-free
standing perimeter.

### 2.3 Move 3 — F2′ becomes assembly over the PROVED O-1thr layer; counting covers D-7b

Answering the dispatch's specific question ("may the O5triple counting route +
O-1thr locality give no-missing WITHOUT the F2 face?"): **for D-7b, YES — verified**:
O5triple Theorem B derives coverage from injectivity + checksums alone ("D-7b coverage
consumes NO no-missing", V18-confirmed pricing, V23 no-critical). **For drainage
(F4-C/OL1-ii), NO** — the run must actually REACH the semantic verdicts, which is a
no-missing use. But check what remains: O-1thr rev 3 PROVED (modulo GD-2/GD-3 at
general states) both halves of local completeness — (M6a) harvest totality (every
(window face, ψ) candidate is harvested, by construction) and (M6c)(ii) no-phantom
(every realized child IS a candidate pair's harvest). Through GD-2/GD-3, window faces
at a realized state = the semantic polygon's sides and their residual factors. So the
induction step "every semantic child of a realized state is realized" is: IH realizes
the prefix (F2 at < N) → F5 identifies the frame (GD-2) → the semantic child is a
window candidate (GD-2/GD-3) → (M6a) harvests it → REAL≡ realizes it. That is
SEM-LAWFUL made concrete: **the F2′ face is the composition of already-proved O-1thr
lemmas with the GD dictionary** — its unit (JC-7, "hardest") should be re-specified as
assembly, not fresh mathematics. The genuinely open inputs are the same GD-2/GD-3
instances everything else needs, plus the REAL≡ repair (GD-6b).

### 2.4 Move 4 — fix the scope/order defects V21 kept

(a) **F3′/tree delta (V21-3):** the tree's O-3 clause 3 still reads "every
fresh-frame-lawful assignment chain"; the design proves the coherent-keyed form. The
tree owes a DELTA 2 line re-keying clause 3 to coherent chains with LC-COH displayed
unconsumed (V21 judged the disposition internally coherent — only the unexecuted tree
edit blocks it). (b) **ADEQ quarantine (V21-5):** ADEQ-surj moves OUT of JC-0 into the
GD-7 unit (upstream, with the O5triple flag duties); JC-0 only TYPE-CHECKS ADEQ.
(c) **Base accounting (V21-6):** the base is "O-2a Theorem 1 at its current grade
(thrice-confirmed conditional structure; pass 2 pending)" — say so, per-face, and let
the cluster's acceptance inherit O-2a's verification state rather than calling the
base proved. (d) G-F1′ gains the multi-lift comparison (now honest under box typing).

### 2.5 The recut cluster, summarized

**K-RUN-BOX** (four faces: no-phantom, no-missing-as-assembly, F4-S/F4-C, F5) by
induction on (N, k); base = O-2a Thm 1; step content = GD-1..GD-6; ADEQ/GD-7 upstream
identifies the target with GMN's t_•(f); F3′-coherent as satellite; O-2b/F6′ evicted
to R-QNT. New-mathematics residue of the whole cluster = the GD families + F4-C's
window bookkeeping (TB-CAP (τ-irr), perimeter-conditional as before) — nothing else.

---

## §3 The recut mandatory path (what is ACTUALLY still open, 2026-08-01 late)

### 3.1 Status board after this week's landings

| node | status now | residue |
|---|---|---|
| O-14a′ | CLOSED per protocol (rescope ratified; RRE(p, ZMod p) formalized, Lean-core; DELTA-1 obligation MET) | Conjecture 5.4.C parked, consumed by nothing |
| O-12 | **VERIFIED** at honest scope (𝔅_n pole-free/(REG-p)-emptiness; V19 + Fable pass 2 clean) | OL-O12-2 + D-11 (instance pin); wording conjunct rides next touch |
| O-13/D-12 | PROVED-UNVERIFIED; V8 in flight; `skeleton_finite` in Lean at every n | D-12r (verdict-pin totality chain, disclosed in §5 (COMP)) |
| Dfloor D-1/D-2/D-4 | V22 pass-1 CLEAN SOUND; pass 2 dispatched | BASE-1(f) fence = classifier side (cluster's business) |
| O-1thr/D-14/D-15 | V24 UNSOUND: ONE critical (REAL≡ non-halted circularity) + gaps; sheared core + Thm 1 + (M6c) perimeter SURVIVED | rev 4: guard restructure (§GD-6 note), DIV1 lift fix, policy/root-kernel perimeter notes; then passes |
| O-2a | V25 SOUND-WITH-GAPS, no criticals, core thrice-confirmed | trim OL-3 consumption to min core (V25 gap); Fable pass 2; residue = GD-1..GD-6 |
| O3design | REJECT ×2 | restructure per §2 (this pass's proposal) |
| O5triple | V23 no criticals, 3–4 gaps (L5b pin wording, (R-0)/(R-1) classification, ledger accounting) | light repair → pass 2; flags = GD-1/GD-7/GD-8 + L5b |
| O-4 | M05/V2 core stands | OL1-ii = F1′-conformance + F4-C + GD-7(b) assembly |
| O-9, O-10 | not dispatched | OL-A/C/D (given GD-3); K-COUNT/K-JAC + D-8 audit |
| D-3, O-8b | not dispatched | adjudicate arbitrary-DVR discipline at GD dispatch; (R1)–(R4) |
| D-11, O-11 | gated | instance pin; then D-9 dependency set |

### 3.2 The path, in dispatch order (replaces DELTA §D1.6's slots 1–11)

1. **Repair wave (verification-only, cheap):** O-1thr rev 4 (the one critical +
   V24 gaps); O-2a OL-3-min trim; O5triple rev 3 (V23 gaps); Dfloor pass 2 rides.
2. **GD-5 composition note** (one page; closes the base seam) + the **S-1 machine
   transcription audit** O-1thr ↔ O-2a stage interface (the audit is the content).
3. **THE GD CAMPAIGN** (the critical mass): one prover unit family for GD-1, GD-2,
   GD-3 (min core first, full form for the value side), GD-8 — stated over an
   arbitrary absolutely-unramified complete DVR from the start (kills most of D-3);
   GD-4/GD-6 as engine-bookkeeping units alongside. Falsifiers: T-E/T-F harnesses
   extended to order ≥ 2 states; the HK52 stretch gate as the standing GD-2(c) trap;
   O2a F5's 871-sample (L3+) harness for GD-8.
4. **The literature unit** (one session): GMN §2.1/§3/§4.1 pulls for GD-1(R-1)/GD-7
   (a)–(c) + L5b normalization + printed-TAMS pagination; MacLane 1936 pin for (V1);
   LIT-3 numbers + Mathlib probe. (LIT-5/BNS: struck, pending the §2.1 OB2 audit.)
5. **Recut cluster** (K-RUN-BOX + F4 + F3′-coherent) per §2.5, plus DELTA 2 tree
   edits (clause-3 re-key; O-2b eviction; D-15 merge; K-OB-C strike).
6. **O-5/D-7 close** (O5triple + cluster interface), then **O-4 OL1-ii** assembly.
7. **O-9** (OL-A/C/D over GD-3-full) ∥ **O-10** (K-COUNT/K-JAC; D-8 guard + consumer
   audit).
8. **D-11 + OL-O12-2** (instance pin; audit OB2's role) → **O-11** (D-9 set: D-8-guarded
   O-10, D-7 triple, O-8b/O-9 weights, D-1/D-11 mass bridge, T-7s) → **root assembly**
   (Phase C; D-1/D-2/D-4 already in hand; Asvin's scaffold shape as the document spine).

### 3.3 Why this is the shortest path

The pre-synthesis view scattered ~22 obligations over seven packages with seven
verification tracks. The merged view shows: (a) FOUR of the eight families (GD-1/2/3/8)
are one mathematical subject — higher-order MacLane/GMN frame-and-residual transport —
already 30% proved (degree-1 perimeter, level-1 census, order-1 conformance) with
standing falsifier harnesses; (b) two (GD-4/6) are engine bookkeeping with proof-by-
construction routes on record; (c) one (GD-5) closes by composition today; (d) one
(GD-7) is a literature-facing unit shared with O5triple's flags. Everything else on
the mandatory path is either assembly over these, an independent quantitative lemma
pair (O-9/O-10), or the instance pin. The eviction of O-2b/BNS/K-OB-C/rates removes
the three most citation-hazardous duties from the critical path entirely.

---

## §4 Formalization-side consolidations now unlocked

* **U-A (`GDInterface`, design-first).** ONE Lean structure carrying GD-1..GD-6 as
  fields (per-order, over the MovesX stage data), replacing the scattered hypothesis
  rows: (M6b)-shaped fences, the OL-2a-* consumption sites, O5triple's (I-1)–(I-3),
  and the cluster's per-face IH plumbing. Every consumer re-keys to the structure;
  a GD family proved retires the field everywhere at once. This is the Lean mirror of
  §1's merge and the highest-leverage consolidation available.
* **U-B (O-12 → Lean; VERIFIED, queued).** The 𝔅_n solve-table family + the pole-free
  theorem: 1×1 kernels, explicit E(e) grammars, Φ_e margins 3/4, 7/8, 6/7 as exact
  rationals; extends `MovesU/RegPFinite.lean`; the ℛ = ℚ[q,1/q,1/(q^c−1)]-unit
  discipline is decidable arithmetic. Parked consumers noted in the ledger.
* **U-C (Dfloor → Lean after pass 2).** Cylinder Haar on ℤ_p^n + MEAS-BRIDGE +
  BRACKET + BASE-CASES — exactly Asvin's verbatim target shape (cylinder-limit density
  + level-k squeeze). This unit yields the capstone RESTATEMENT spine; NOTE: touching
  the capstone statement is a parked-class item needing sign-off — build the new
  statement alongside, map via D-1/BRACKET, swap only on approval.
* **U-D (O5triple Theorem B, abstract; immediate).** "Injection with equal weighted
  checksums and positive weights is a bijection" — ~20 lines, unconditional, no GMN
  content; gives the D-7b mechanism a permanent Lean core.
* **U-E (WGEO/VTX degree-1 perimeter → Lean).** VAL1/KEY1/DIV1/WGEO/VTX against
  MovesX: retires the (M6b)(i) and (N4)-upper interface rows in the Lean corpus and
  is the semantic twin of HK-11a (the e′ = 1 vertex law) — the WGEO vertex pin
  u_μ = γ IS the transport content whose e′ ≥ 2 failure HK52 compiled; formalizing it
  documents WHY the guard is e′ = 1.
* **U-F (skeleton consumer wiring).** After V8 accepts O-13: unwire the hfin fence per
  the recorded import-order block (already parked; no new proof).
* **U-G (O-2a order ≤ 1 → Lean).** Theorem 1 + Lemma R at the 𝔈 carrier (MovesX
  types exist); the order-1 conformance layer is where the L3/L4 verified counting
  cores already live — a natural round-trip #4 after M09/M17/O-13.

Dispatch note: U-D and U-A(design) cost hours; U-B/U-E are prover-unit sized; U-C/U-G
wait on their pass-2s. None of these blocks the math path; U-A actively accelerates it
by making the GD merge enforceable in the corpus.

---

## §5 Proposed DELTA 2 lines for the tree (orchestrator adjudicates; NOT applied)

1. O-3 clause 3 (nonempty locus): re-key "fresh-frame-lawful assignment chain" →
   "coherent chain (HistoryCoherent)"; LC-COH displayed as a non-consumed open note.
   [V21-3; the design's §R2 disposition confirmed coherent.]
2. O-2b (K-DICT-OB1/MF-MATCH/TT-DET′): move from the critical path to route R-QNT
   (D-16's package), per O3design §4's consumer table + §D1.4. OB2: conditional on the
   D-11 audit (§2.1). LIT-5: LITERATURE-CANDIDATE, R-QNT-only.
3. D-15: merged into the recut cluster's deliverable (K-RUN-BOX corollary + O-1thr
   Thm 3); K-4's repair pointer follows.
4. K-OB-C: struck from the mandatory set (O-7/R-QNT only); the no-phantom warrant is
   the GD dictionary per O3design's intra-step order.
5. New named nodes: **GD-1..GD-8** (this file §1) with the consumption mappings as
   the statement-level cross-index; O-1/O-2a/O-3/O-5/O-9 residues re-pointed at them.

— SYNTH4 complete, 2026-08-01 late. Deliverable of the standing synthesis duty;
next synthesis pass after the GD campaign's first wave reports.

