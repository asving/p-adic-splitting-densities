# O3adj — the O-3 ⊕ O-2b design after TWO REJECTs: adjudication + replacement skeleton (Fable, 2026-07-31)

**Unit type: ADJUDICATION.** Charge: V16 (`V16_o3design.jsonl`, 6 blockers + 8
advisories) REJECTED the O3design rev-0 statement layer; V21 (`V21_o3design2.jsonl`,
5 blockers + 1 advisory) REJECTED REVISION 1. Two consecutive REJECTs ⇒ judge the
APPROACH: classify V21's findings against V16's, then decide (a) revise again (only
if V21's blockers are localized) vs (b) REPLACE the joint-induction design with a
composition of the already-converging pieces (O5triple's counting-forced coverage +
O-1thr rev 3's (M6c)-locality + O-2a rev 4's OL-6-bound dictionary). The SYNTH4
agent runs the same question from the other side; outputs cross-read.

Sources: both full reports; `O3design_phaseB_attempt.md` (rev 0 §§0–7 + REVISION 1
§§R1–R6, kept byte-stable there); `O5triple_phaseB_attempt.md` +
`O5triple_phaseB_verifybrief.md` §5 (the interface, read verbatim);
`O1thr_phaseB_attempt_rev3.md`; `O2a_phaseB_attempt_rev4.md`;
`docs/MATH_COMPLETION_TREE_2026-08-01.md` (O-3/O-4/O-5/O-7 node texts, D-13/D-14/
D-15/D-16, §D1.3, §D1.4, §D1.6).

## 1. Classification of V21's findings (repeat / new-from-revision / fresh-in-confirmed)

| # | V21 finding (compressed) | class | localized? |
|---|---|---|---|
| 1 | F1′ not selected-f: Run_N(x) is box-only, F1′ is ∀-separable-f, so two lifts of one box reconstruct the every-lift clause; the D-15 quarantine fails | **REPEAT-IN-SUBSTANCE of V16-5** — the rev-1 repair (withdraw the clause, keep the box-keyed ∀f statement shape) is syntactic; the quantifier is intrinsic to the shape | **NO** — attacks the architecture (box-keyed global theorem), not a wording |
| 2 | F4-S/F4-C carry the same hidden lift quantification | same family as #1 (V16-5 reconstructed through the rev-1 F4 split) | **NO** — same structural root |
| 3 | F3′ serves the consumer table but the governing tree still says "every fresh-frame-lawful chain"; the re-key is only a recorded, unexecuted delta | **NEW-FROM-REVISION** (design-vs-tree governance mismatch created by the F3′ re-key) | YES — execute the recorded tree delta |
| 4 | F6′ right-sized, but ≈/pooling must be proved congruences for verdict/acceptance decorations; truncation maps on quotients need well-definedness | **NEW-FROM-REVISION**, advisory | YES — statement-layer obligations (and moot for the root under replacement: deferred with D-16) |
| 5 | ADEQ not operationally quarantined: the open surjectivity leg is load-bearing for recovering the tree's O-3, depends on OL-2a-1 dispatched later, "JC-0 FIRST" cannot prove it; PROVED/conditional labels compounded | **REPEAT-IN-SUBSTANCE of V16-1** — the target-replacement blocker survives as a named-but-open, load-bearing lemma with an incoherent dispatch order | **NO** — the Cons^τ-defined global T_can needs a global adequacy theorem by construction |
| 6 | G-F1′ misses the cross-lift consequence; G-LIFT mis-attributed (full-run-set lift comparison is D-15/CYL-level, not O-1thr/D-14); "proved base" overstates SOUND-WITH-GAPS material | **MIXED** — the gate half rides #1 (the quantifier is still there, so no per-box gate tests it); the base half repeats V16-14's overstatement | derivative of #1/#5; the base-language and G-LIFT-attribution fixes are localized |

**Tally:** 3 of 6 findings (all three the heaviest blockers: 1, 2, 5) are V16's two
central blockers surviving their own repairs; 2 are new-from-revision and localized
(3, 4); 1 is derivative (6). **Zero findings land in byte-stable confirmed
territory** — there is no fresh-in-confirmed churn; the verifier is converging on
exactly two points, and both are architectural:

* **(P1)** Any box-keyed global statement "∀ f : Run_N(f mod p^N) = (semantic tree
  of f)_{≤N}" carries the every-lift/cylinder law INTRINSICALLY (instantiate at two
  lifts of one box). Right-sizing the wording cannot remove it — twice demonstrated.
* **(P2)** Defining the semantic object as the Cons^τ-set forces a global adequacy
  theorem (ADEQ) with an open surjectivity leg that no dispatch order can put first.

## 2. The decision: (b) REPLACE — with the displayed argument

Criterion check for (a): V21's blockers would need to be localized. Findings 1/2/5
are not (§1) — they refute the two moves that DEFINE the joint-induction design (the
box-keyed six-face package IND(N); the Cons^τ-defined T_can). A third revision would
have to abandon both, i.e. would be a replacement wearing a revision's name.
**Decision: (b).** The affirmative case is that the replacement already exists in
pieces, each with its own hostile-verification record:

**(Arg-1) OB1 has no root-mandatory consumer — the mutual induction has lost its
reason to exist.** The V6-finding-23 cycle was: O-2b's trace correspondence
(K-DICT-OB1) quantifies over the classifier's produced trees (O-3's subject), so
D1.3 joined them into ONE cluster proved by mutual induction. Walk the consumers of
OB1: D-16 (READ-δ execution transport) — the tree marks it "OPEN (optional for the
root — rates only; see §D1.4)"; O-7's tree/iteration correspondence — O-7 is
route-R-QNT, struck from the root-mandatory set (§D1.4); O-6 — likewise. The one
apparent critical-path consumer is O5triple's interface clause (I-1), whose
ATTRIBUTION line says "composed with ... the trace correspondence = O-2b". But the
displayed CONTENT of (I-1)(a)–(c) (`O5triple_phaseB_verifybrief.md` §5, read
verbatim) is single-polynomial: for every lift g a map β_g from the box's engine
leaf slots into g's semantic tree 𝒯(g), path data through OL-2a-2/3, verdicts
through O-2a Theorem 2 — no ∼_OM pair, no second polynomial's RUN anywhere. What
(I-1) needs is the dictionary (O-2a) + per-site lift transfer below thr(T) ≤ N
(O-1thr Theorem 1 / D-14), NOT the cross-polynomial K-DICT-OB1. So OB1 (with
TT-DET′/MF-MATCH and finding-4's congruence obligations) defers intact to the
D-16/rate tier, and the cycle DISSOLVES rather than being broken by induction.

**(Arg-2) Counting-forced coverage replaces global no-missing for the assembly
consumers.** O5triple Theorem B (verifier target on file, falsifier 1341/1341):
transport injectivity (I-2) + the two checksums Σ e·f = n (engine typing (I-3);
semantic Theorem A(4)) force β_g ONTO the semantic leaves by pure counting — "D-7b
needs NO no-missing clause" is that note's headline dependency sharpening. So the
hardest face of the old design (F2, global no-missing) is not what O-5 + D-7a/b/c
consume; and ADEQ's leaf-level surjectivity is counting-forced for free.

**(Arg-3) What no-missing residue remains is ONE ordinary induction with a fixed,
already-proved-at-perimeter per-site step.** O-1thr rev 3 proved (at the displayed
perimeter: root states + degree-1 first transitions outright; (V1)/(V2)
citation-grade beyond) exactly the per-site kernel: roster totality
((M6a) + (M6c) + SPAN/Corollary VTX — every side/residual profile readable at the
state is on the menu, no phantoms, beyond-window excluded), and REAL≡ (read ∧
lawful = realized, conditional on (M6a)+(M6b)+(M6c)). D-14 (lawful-site locality,
in flight) localizes each lawful read. O-2a rev 4's OL-6 (run decomposition + chain
binding, EVERY level — the single general glue law its class-(a) churn discipline
produced) binds the engine's state after a realized prefix to the stage read over
Θ(prefix). Iterating per-site roster totality + D-14 + REAL≡ along a chain, with
the state carried by OL-6, IS no-missing for the selected f — an induction on chain
length whose IH contains no O-2b face, no F6, no cross-polynomial anything. O-2a
rev 4 §3 flagged precisely this ("the O3design ledger should consume OL-6 as the
binding premise, not re-derive per-level glue"): the composition executes the flag.

**(Arg-4) The twice-rejected quantifiers land in owners that already exist.** (P1)'s
lift content lives at O-1thr Theorem 1 (per-site two-lift transfer below the
ceiling — PROVED outright for the repaired machine) and at D-15 (the cylinder node,
already on the critical path at attack-order slot 2, with the ns-guard explicit) —
the composition states NO box-keyed universal theorem, so there is nothing to
reconstruct. (P2)'s interior adequacy becomes per-site SPAN totality carried as a
clause of the same induction (Arg-3), and its leaf surjectivity is Arg-2's counting
— no global tree-isomorphism lemma remains, so V21-5 has no object to land on.

Similarly, no-phantom is not a new induction at all: O-2a Theorem 2(D) (each emitted
record = the GMN datum of the stage read over its emitted prefix's chain, modulo
OL-2a-1..6) IS no-phantom in dictionary form, and its run-length induction is
already written inside O-2a rev 4 §5. The composition's coupling between its two
single inductions ((D)'s, and Arg-3's) is through FIXED per-site lemmas only —
**no new mutual induction.**

## 3. THE COMPOSITION MAP — the replacement skeleton (node K-RUN-C)

Standing preconditions unchanged (tree §2.4): f monic separable ns-free of degree n
over O; ns-free carriers; pinned F_rep. All statements are PER-f (selected-f); box
quantification appears only where D-15 owns it. N\*(𝐇) = the D4R.4/L12 per-branch
level (rev-1 (O5′), uncontested by V21) with the TB-CAP verdict-window join; CEIL-UB
retained as the one-directional bound (all K-OB-A needs).

### 3.1 Units

* **CU-1 (NM — no-missing + interior adequacy + state binding; THE one new proof).**
  Statement (two clauses, one induction on chain length k): for every Cons_f chain 𝐇
  with N\*(𝐇) ≤ N — (i) the canonical run on f at working level N realizes 𝐇
  (REALIZED in O-1thr rev 3's single displayed sense); (ii) the engine's frame state
  after the realized prefix equals the stage data of Θ(𝐇) (the OL-6 binding; the old
  F5 content, now a carried clause, not a face). Step = IH + OL-6 + OL-2a-2-min/3
  (state identification) + SPAN/(M6a)/(M6c)/VTX (the semantic next read is
  menu-lawful — the old SEM-LAWFUL, now literally O-1thr's roster totality at the
  identified state) + D-14 (lawful ⇒ read determined below L(H,ν)) + REAL≡. Base =
  O-2a Theorem 1 + the OL-5 order-1 base, statuses displayed VERBATIM
  (PROVED-UNVERIFIED / SOUND-WITH-GAPS — no "proved base" phrase; V21-6 accepted).
  Interior adequacy: clause (i)'s converse direction at the GMN side (every t_•(f)
  node arises from a Cons_f chain) is per-site SPAN totality inside the same step —
  ADEQ as a global unit is DELETED.
* **CU-2 (NP — no-phantom).** = O-2a Theorem 2(D) ∘ ι: every emitted record of the
  canonical run on f is the GMN datum of its chain — consumed from O-2a rev 4,
  residue exactly OL-2a-1..6 (declared there; nothing re-derived here). **CU-2t
  (terminal seam):** the old Cons^τ (t-i)/(t-ii) obligations, one lemma from O-2a
  Theorem 2(B) saturation + TB-CAP (τ-hen)/(τ-irr) windows — kept, since verdict
  records still need their forced-terminal reading; no global T_can definition rides
  on it anymore.
* **CU-3 (NE — nonempty locus, coherent form).** = O-14a′ RunRealizerExists (ZMod p
  collapse + last-node closure, verifier-confirmed) + D-14 cylinder pinning + the
  (O6) canonicalizations for census bookkeeping. REQUIRES executing the recorded
  tree delta (O-3 clause 3 re-keyed to coherent chains; LC-COH displayed open,
  unconsumed) — V21-3's fix, a governance action due under EITHER decision.
* **CU-4 (ACC — acceptance, selected-f).** F4-S (soundness, every N) + F4-C
  (completeness at N ≥ N\*) exactly as rev-1 split them (V21 confirmed the level
  quantifiers right-sized), stated for the box's own f only; from O-1thr Theorem 3
  (F1)/(F4) + O-2a Theorem 2(B) + TB-CAP (τ-irr) window [perimeter-conditional,
  displayed].
* **CU-5 (satellites).** K-OB-A = O-1thr Theorem 1 per site + O-13/D-12 roster
  finiteness (corollary-grade). K-OB-B = the DES-6 re-key + CU-1 (definitional +
  one N\* computation). K-OB-E = GMN Def 3.9 (near-definitional). K-OB-C = standalone
  GMN-side unit, citation pull first (old JC-11, unchanged).
* **CU-6 (OB2 — σ-invariance).** Level-free: O-2a clause (i) + BNS §2 transcription
  (Defs 1.7/3.1–3.2 pinned) — old JC-12 unchanged; V16-9 confirmed the evasion.
* **CU-7 (O5triple interface discharge + re-attribution).** (I-1)(a) = CU-2 +
  O-1thr Thm 1/D-14 lift transfer at the run's sites below thr(T); (I-1)(b) = CU-2t
  + CU-4 + Lemma STEEP (already O5triple's); (I-1)(c) = O-2a Theorem 2(B)/(D);
  (I-2) = OL-2a-2/3 faithfulness + the (N4) corner band (O-1thr). ACTION: correct
  the O5triple brief's attribution line — its (I-1) content consumes NO K-DICT-OB1;
  the "∘ O-2b trace correspondence" phrase priced to a node the content never uses.
* **DEFERRED TIER (route R-QNT; not root-mandatory).** OB1 = F6′ + TT-DET′ +
  MF-MATCH + the V21-4 congruence/well-definedness obligations + D-16 + gates
  G-F6′/G-MF. Rev-1's right-sized statements are the tier's starting spec — the two
  review rounds' work on them is banked, not discarded. Opens only if Phase C elects
  explicit rates (OL2) or the T-9 quantitative route.

### 3.2 The consumer-table walk (every O-3/O-2b consumer, served or deferred)

| consumer (tree node) | needs | composition supply |
|---|---|---|
| K-14 MarkGraft (I0) | grafted realized censuses extend | CU-1 + CU-3 |
| K-14 (I1) faithful census | realized = semantic counts per box | CU-1 + CU-2 (per f) + **D-15** (box level — owns lift-uniformity, ns-guard explicit) |
| K-14 (I3-rc) | frame-state premise at recenterings | CU-1 clause (ii) |
| O-4 OL1-ii | run terminates below N(f), Cert accepts there | CU-2 + CU-4 (F4-C at the decision level) + GMN Cor 4.19 |
| O-5 + D-7a/b/c | interface (I-1)–(I-3) | CU-7 (no OB1 — Arg-1/Arg-2) |
| O-7 (X1)/(X4) | no-phantom + K-OB-C/K-OB-E | CU-2 + CU-5 [O-7 itself is route-R-QNT] |
| D-15 (CYL) | D-14 + (K2) + no-phantom/no-missing + (τ-irr) | D-14 + O-1thr Thm 3 + CU-1/CU-2 + TB-CAP |
| D-16 (δ transport) | OB1 + OB2 + F1–F5 | **DEFERRED** (root-optional, §D1.4) |
| D-11 / mass-id | σ-invariance | CU-6 |
| K-4/K-6 repairs | via D-15 | indirect |

Display: every root-mandatory consumer is served WITHOUT any box-keyed universal
theorem, without ADEQ, and without OB1; the unserved consumers are exactly the
tree's route-R-QNT set. This is the check the charge asked for.

### 3.3 Honest residue ledger (open after the composition; owners named)

1. OL-2a-1..6 — O-2a's declared residue (units = old JC-1..4 pattern + OL-5-min +
   OL-6); OL-6's falsifier = G-EMIT (recorded at O-2a rev 4 §4).
2. O-1thr residue — (M6b)(iii) AUX + lower (N4) band (REAL≡'s only consumption) +
   (V1)/(V2) exact attributions + the (E-N) caveat.
3. D-14 — in flight (pass-1 substantively clean, r2 pending).
4. **CU-1's induction itself** — the composition's ONE new proof obligation.
5. CU-2t; TB-CAP (τ-irr) perimeter (T-6/D-12r, inherited-conditional, displayed).
6. K-OB-C citation pull; LIT-1/BNS transcription duties (unchanged).
7. Tree deltas (§3.5). LC-COH — displayed open, consumed by nothing.

### 3.4 Gates (carried, re-attributed per V21-6)

U6 length-3 (G-F1/G-F2/G-F5, selected-f kill criteria); **G-LIFT re-attributed**:
its per-site read comparison tests O-1thr Thm 1/D-14, its full-run-set lift
comparison is D-15's gate and moves there; G-F3′ (coherent-chain kill only); G-F4′
(all-N sweep, split kills); G-CEIL′ (both directions: N\* ≤ working level kills
CU-1's precondition bookkeeping, N\* ≤ max-ceilings kills CEIL-UB); G-EMIT (now also
OL-6's falsifier); G-OB2 (free rider, kept); G-OBC. G-F6′/G-MF → deferred tier. The
O-1thr rev-3-recommended DEPTH-3 falsifier (order-2 states, where (V1)/(V2) are
genuinely consumed) is promoted to CU-1's primary gate: it exercises every per-site
ingredient of the new induction's step exactly where they are weakest.

### 3.5 Tree deltas to execute (governance actions, sign-off owed)

1. §D1.3 item 2: retire "ONE joint cluster, proved together by mutual induction on
   resolution level"; replace with the K-RUN-C composition (§3.1) + the deferred
   OB1/D-16 tier. O-2b's OB1 half moves to the D-16 node; OB2 stays root-side (CU-6).
2. O-3 clause 3: re-key "every fresh-frame-lawful assignment chain" to the coherent
   form, LC-COH the displayed residue (the rev-1 recorded delta — V21-3).
3. O-3's "of any lift f" phrase: re-point to D-15 routing (per-f faces here).
4. O5triple brief attribution line correction (CU-7).
5. §D1.6 critical path: "[O-3 ⊕ O-2b joint cluster]" → "[K-RUN-C composition:
   CU-1..CU-7]"; dispatch order = CU-1's gate (depth-3 falsifier) → CU-1 spec →
   the rest as §3.1's consumption arrows dictate.

## 4. Risk display (what could still kill the replacement)

* **R1 (highest):** CU-1's step at deep states rides (V1)/(V2) (MacLane
  multiplicativity + the GMN key/development dictionary) and REAL≡'s (M6b)(iii)+
  lower-(N4) perimeter — the depth-3 falsifier is the cheap pre-test; a kill there
  reopens the per-site kernel, not the composition's shape.
* **R2:** the (E-N) caveat (can a level-N box fiber a thr > N tree?) touches CU-4's
  decision-level completeness through O-1thr Thm 3(c)'s scoping — displayed OPEN.
* **R3:** if a future consumer is found that genuinely needs cross-polynomial OB1 on
  the critical path (the walk in §3.2 says none exists today), the deferred tier
  re-opens — with rev-1's right-sized F6′/TT-DET′ as its spec, plus V21-4's
  congruence obligations. That is a re-scoping event, not a silent assumption.
* **R4:** K-14's census granularity — if (I1) turns out to need per-box semantic
  counts BELOW leaf level with lift-invariance, that is D-15 content by §3.2's
  routing; D-15 sits at attack-order slot 2, upstream of every consumer that could
  fire this.

## VERDICT

**REPLACE (decision (b)).** V21's three heavy blockers are V16's two central
blockers surviving their own repairs — structural to the box-keyed six-face mutual
induction and to the Cons^τ-defined global T_can, hence not revisable (§1, §2
criterion). The replacement is the K-RUN-C composition (§3): no-phantom = O-2a
Thm 2(D)/OL-6 (induction already inside O-2a); no-missing + adequacy + state
binding = ONE new ordinary induction (CU-1) with an entirely per-site step already
proved at the O-1thr rev-3 perimeter; coverage at leaves = O5triple's counting
(no no-missing consumed); nonemptiness = O-14a′ + D-14; acceptance = O-1thr Thm 3 +
O-2a 2(B) + TB-CAP; OB2 level-free; OB1 + D-16 deferred to the rate tier with no
root-mandatory consumer lost (§3.2 walk). No mathematics is claimed proved by this
adjudication. Next: cross-read against SYNTH4's output, then the §3.5 tree deltas
(sign-off), then CU-1's depth-3 gate before its spec dispatches.

