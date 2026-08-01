# R11 REPAIR DESIGN (2026-08-03) — restoring the composition after the D-11 owed-pass refutations

**Status of this document: DESIGN ONLY — now at REVISION 2 (2026-08-04).** No edit to
ROOT (`docs/ROOT_ASSEMBLY_2026-08-02.md`, REVISION 9, a2ad88a) and no edit to the D-11
leaf (`lean/notes/openmath/D11_massid_phaseB_attempt_rev3.md`, 8a0786c) is made here.
This design goes to a Codex plan-review BEFORE execution; §7 lists the execution units.

## REVISION 2 record (2026-08-04) — the plan-review criticals folded

The Codex plan-review of REVISION 1 returned **DESIGN-REVISE** (report:
`R11D_review_2026-08-04.md` — findings 1–5 and 9 CRITICAL, findings 6–8 ADVISORY; the
dispatch counted "5 criticals" = findings 1–5, finding 9 being the execution-order
ruling, folded here at §7). REVISION 2 is produced by editing the REVISION-1 body IN
PLACE at exactly the sections each finding hits; every REVISION-1 passage not named in
the table below is byte-stable. Dispositions (no silent drops):

| # | review finding (gist) | class | disposition | where |
|---|---|---|---|---|
| 1 | (RE) is NOT definitionally discharged (the O-12 quotes do not pin the consumed member's per-block booking profile; absence-of-α does not prove the full profile; M1′'s pin is in-chain assertion); (PACK-iv) is warranted | CRITICAL | **ACCEPTED — (PACK-iv) PROMOTED to the PRIMARY route**; the definitional discharge WITHDRAWN with the reasons recorded verbatim; the (RE) analysis kept as (PACK-iv)'s named RETIREMENT ROUTE; E4 presents (PACK-iv) as a NEW hypothesis member, never a clarification | §3.3, §3.5, §4 N5, §7 E3/E4 |
| 2 | (b-SW) is asserted, not proved from the quoted grammar; {loop-0 forever} is not a finite word and sits outside (b-PF) | CRITICAL | **ACCEPTED — (b-SW) REPLACED by the OPEN LEMMA (b-EX)** (grammar exhaustiveness), stated verbatim with its proof route (induction over the displayed seven-family grammar + the three booking adjustments) as a D-11 r4 proof obligation, the case-check sketch displayed in-design; the infinite loop-0 word handled by the separate displayed null/disjointness note **(LOOP-∞)** | §2.4, §4 N1, §7 L4/E1 |
| 3 | the M3(a) narrowing may lose content N2 needs (Haar-nullity ≠ exact classification / finite-level counting / weight-preserving regrouping); the certificate implication was pointed at, not checked | CRITICAL | **CONSUMER-SIDE CHECK EXECUTED for this revision** (sources read: O-1thr §1.4 + Theorem 3; M04 Theorems 1–2 / Lemma 3.3 / Theorem 4; ROOT Step 18 K1/K4): every K1 box receiving a verdict label fibers a decided NS-FREE tree BY THE DISPLAYED CORPUS DEFINITIONS — displayed as **Lemma (K1-NSF)** with the two-channel consumption attribution; (NS-ALL) stays a labeled contingency, now narrowed | §2.5, §4 N2, §7 E9 |
| 4 | N1 silently uses content outside repaired M1 (member-row Σ = 1 via "canonical grammar + family-(vi) aggregates"); β-leg normalization source unnamed; circularity risk with Step 18b | CRITICAL | **TRACE EXECUTED**: member-row Σ = 1 is consumed NOWHERE on the mandatory path — the REVISION-1 N1 delivery claim is WITHDRAWN; the only normalization-class law at Step 18 is (PACK-ii) (already priced); the contingent route **(ROW-Σ)** is displayed (block induction, M2-free, non-circular); the 18-vs-18b dependency chains displayed | §4 N1 + (†18), §6, §7 E1 |
| 5 | the M2.0 repair is plausible but not a discharged proof; obligations omitted (union identity, infinite pre-hand-off path, measurability, law preservation, per-block a.s.-exit use) | CRITICAL | **ACCEPTED — the obligation list COMPLETED**: (O-1)–(O-5) enumerated verbatim, each with its displayed route; "billing unchanged" demoted from established fact to the design-level claim the r4 proof must bear out | §3.4, §4 N4, §7 L6 |
| 6 | BOX-VOL is a genuine local demonstration; r4 should verify k counts distinct imposed equalities + every N(P) occurrence's provenance | ADVISORY | r4 duty ADDED to L2 | §7 L2 |
| 7 | "clause (c): per sub-clause as displayed" is not a scope statement; "proof obligations: none" too strong absent a downstream "mass"-word sweep | ADVISORY | §2.1's repaired preamble gains clause (c)'s per-sub-clause reference measures; L1 gains the sweep of every downstream unqualified "mass" | §2.1, §7 L1 |
| 8 | (H8) correctly treated (possible overpricing, not concealment) | ADVISORY | no change | §5.1 |
| 9 | execution/acceptance order unsound: Unit B not conditioned on r4 ACCEPTANCE; E8's counter-to-zero conflates "no recorded leaf critical" with "composition accepted" | CRITICAL | **ACCEPTED**: Unit B now CONDITIONAL on the r4 hostile pass ACCEPTING; E8 restated — every standing display stays **SUSPENDED** until the NEW end-to-end bar passes; the counter shows 0-of-2 toward that bar and never reads "clean" | §7 E8 + Order |

**The revised bottom line (supersedes REVISION 1's "BLOCKED: NONE" — which the
review correctly ruled unsupported).** No need is blocked in the strict ledger sense
(every need has a displayed route: a proof on file, a priced [M] member, or a named r4
proof obligation with a displayed proof route and a hostile-pass bar), but the flat
"all MET" is WITHDRAWN. Honest tiers, argued need-by-need at §4: N3/N6 MET on file;
N2 MET by the executed check; N5/N7 MET AT PRICE (one NEW [M] member, (PACK-iv));
N1/N4 **MET-PENDING-r4-PROOF** ((b-EX); (O-1)–(O-5)) — the composition is NOT restored,
and the acceptance standing does not move, until those discharge under the D-11 r4
hostile pass.

**What happened (self-contained).** The ROOT composition assembles the uniformity
theorem (splitting-type densities of Haar-random monic degree-n p-adic polynomials are
values R_τ(p) of single rational functions, at every prime including wild) as a linear
walk of 19+ steps over verified/proved-unverified leaves, with all open mathematics
priced in named hypothesis rows (H1)–(H7) ("[M] rows"). Its Phase-C acceptance
(2026-08-03) was SUSPENDED the same day: the owed hostile pass on leaf D-11
(`D11_owedpass_2026-08-03.md`, Codex, fresh context) returned CRITICAL findings, and
the impact audit (ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md`, 44ce0a7) showed two
MANDATORY ROOT steps consume the refuted layers AS PROVED:

- **Step 17** consumes D-11 **Theorem M1** (mass identification: the abstract solve
  family 𝔅_n's entries ARE Haar masses of continuation events) — refuted at its
  announced conditioning scope (C1), at the family-(v) per-entry mass claim (C2), at
  its §5/§7 billing (C3), and at its multi-step disjointness clause M1(b) (C4).
- **Step 18b** consumes D-11 **Theorem M2** (the solved values ARE the real
  conditional densities) — FALSE at its displayed universal scope (C6: arbitrary
  allocation data satisfy (S1)/(S2) yet destroy the mass reading; the proof mis-cites
  M1(a) at family-(iv) verdict rows). GAP G5 (Lemma M2.0's address induction omits
  within-block loop history) sits in the same consumed chain.

Also owed from the same campaign: **O11-G2** — the CUT-WD premise of Step 18's
consumed walk has no ROOT display and no [M] home; and the O-11 leaf-side n ≥ 2
Lean-guard note. Both dispositioned at §5.

**The decision per layer (summary).**

| finding | decision | mechanism |
|---|---|---|
| D11-C1 (M1 conditioning scope) | TRUE-SCOPE REPAIR | per-clause reference-measure display; no formula changes (§2.1) |
| D11-C2 (family-(v) L6a factor) | TRUE-SCOPE REPAIR | the relaxed-box event □(P) + Lemma (BOX-VOL), 2-line proof over L6a's own displays (§2.2) |
| D11-C3 (billing contradiction) | display repair | §5/§7 re-billed to match (a″) exactly (§2.3) |
| D11-C4 (M1(b) disjointness) | TRUE-SCOPE REPAIR | (b-PF) prefix-free lemma (argued in-design) + **(b-EX) grammar-exhaustiveness OPEN LEMMA** (r4 proof obligation; induction sketch over the displayed grammar, §2.4) + the **(LOOP-∞)** null/disjointness display for the infinite loop-0 word [REVISION 2] |
| D11-G5 (M2.0 addresses) | TRUE-SCOPE REPAIR | loop-extended addresses; two-letter transport induction (loop letters ← L2/L3 PROVED, hand-off letters ← (S1-m)); r4 obligations **(O-1)–(O-5)** enumerated with routes; billing (S1-m)+(DET) = the design-level claim the r4 must bear out (§3.4) [REVISION 2] |
| D11-C6 (M2 false at scope) | TRUE-SCOPE REPAIR + [M] PRICE [REVISION 2] | Theorem M2 restated AT the hypothesis (RE): all blocks booked re-entrant — then verdict rows are canonical BY THE VERIFIED 𝔅_n GRAMMAR (α exists only at (O2)). At the CONSUMED member, (RE)+row-form = **(PACK-iv)**, a NEW (H5) row-law member — the PRIMARY route; the REVISION-1 definitional discharge is WITHDRAWN (review finding 1); the (RE) analysis survives as (PACK-iv)'s RETIREMENT ROUTE (§3.3/§3.5) |
| D11-C7 (M3(b) silent clause 4) | leaf statement hygiene | conditionality moved in-statement; ROOT already insulated at (H5) (§2.7) |
| D11-G8 (M3(a) "EVERY polynomial") | TRUE-SCOPE REPAIR | conclusion at separable lifts (= Theorem E's scope) + ns-null mass-sufficiency note; consumer-side check EXECUTED at REVISION 2 — **Lemma (K1-NSF)** displayed with the two-channel attribution; contingency (NS-ALL) flagged, narrowed (§2.5) |
| D11-G9 (falsifier criterion) | display repair | criterion rescoped to (a″)'s families (§2.6) |
| O11-G2 (CUT-WD) | [M] PRICE | NEW row **(H8) = (K-CUT)**, with the O-11 charge-(vi) adjudication as named retirement route (§5.1) |
| O11-C1 residue (n ≥ 2 guard) | leaf/Lean note | O-11 r4 restates the target row at n ≥ 2; BK.series_tie carries the guard at formalization (§5.2) |

**BLOCKED list [restated at REVISION 2; the REVISION-1 "EMPTY" was unsupported]:**
strictly EMPTY (every need has a displayed route), but stratified honestly — N1/N4
are MET-PENDING-r4-PROOF and N5/N7 MET AT PRICE ((PACK-iv), NEW (H5) member, plus
(H8)); §4 runs the check need-by-need with the tiers displayed. Labeled
contingencies (not blockers) at §6.

---

## 1. Objects and vocabulary used below (minimal, for the fresh reviewer)

D-11 works over the O-12 semantic model (VERIFIED leaf: `O12_phaseB_verifybrief_rev4.md`):
q₀ = p^δ, K₀/ℚ_p unramified, O its integers, Haar on monic degree-e polynomials via
coefficient tuples O^e; E := e(e+1)/2; C_e := {v(a_i) ≥ 1 ∀i} the block-e state law;
R_e := {v(a_i) ≥ i ∀i} the descent event. One step of the descent process 𝒟_e
stratifies C_e into loop strata ((loop-0), (loop-c) for c ∈ F_{q₀}^×), pattern strata
(patt-π), and polygon strata (poly-κρ⃗), up to the null set Z_e; κ₀ := P(loop-0|C_e) =
q₀^{−E}, κ₁ := P(⋃_c loop-c|C_e) = (q₀−1)q₀^{−E}. The abstract solve family 𝔅_n
(O-12 §2.3) has per-block entry tables E(e) in seven families: (i) kernels,
(ii) divisor-pattern masses m(π), (iii) polygon-family masses m(κ,ρ⃗), (iv) verdict
rows, (v) scalar atoms {q^{−b}} ∪ {(q^d−q^{d−1})^{−1}} ∪ {(q−1)/(q^{n+1}−1)} ∪
{q^{E_m}/(q^{E_m}−1)}, (vi) β-legs, (vii) solved entries β_e(σ) = u^{−1}t_σ. Four
BOOKINGS (O1)/(O2)/(O2′)/(O3) fix which strata are booked as loop vs exit; the
RE-ENTRANT bookings are (O1)/(O2′)/(O3). D-11's Theorem M1 identifies entry values
with stratum masses; Theorem M2 identifies solved values with true conditional
densities given seams (S1) (hand-off faithfulness, ← ROOT Step 14) and (S2)
(composition-datum correctness, ← ROOT Step 18); Theorem M3 ties row labels to true
types. ROOT consumes: M1/M1′/M3 at Step 17, M2 at Step 18b, the actual-pack
correspondence + row-laws as hypothesis (H5) = (PACK) with clauses PACK-i (rsh_interp),
PACK-ii (r_bdd), PACK-iii (wsh_ok).

---

## 2. LAYER M1 (consumed at ROOT Step 17): true-scope repairs

### 2.1 C1 — the conditioning scope (statement repair, no formula changes)

**Defect (verifier, verbatim gist).** M1's preamble announces "with all masses
CONDITIONAL on the state law C_e", but (a′) reads vol(C_e) = q₀^{−e},
vol(R_e) = q₀^{−E} — AMBIENT Haar masses (P(C_e|C_e) = 1, P(R_e|C_e) = q₀^{−(E−e)});
the singleton-residual readings are conditional on a CELL. "M1 does not have one
coherent meaning of 'mass'."

**Verification that the defect is preamble-only.** Every clause-(a) bullet is
coherently conditional-on-C_e as displayed: (O1) q₀^{−(E−e)}·q₀·q₀^{−e} = q₀^{1−E};
(O2) q₀^{−(E−e)}·q₀^{−e} = q₀^{−E}; (O3) κ₁/(1−κ₀); the pattern bullet carries
q₀^{−(E−e)} = P(R_e|C_e); the polygon bullet carries the displayed conditional
normalization q₀^{+e}. The verifier found no arithmetic error anywhere (M1′'s
arithmetic "survives checking"). The repair localizes to the preamble + (a′).

**REPAIRED PREAMBLE (verbatim; replaces "Then, with all masses CONDITIONAL on the
state law C_e:").**

> Then, with the reference measure NAMED PER CLAUSE — clause (a): masses CONDITIONAL
> on the block state law C_e (each bullet displays its conditional derivation);
> clause (a′): per occurrence as displayed there (AMBIENT Haar on O^e for the
> valuation-box readings, with the conditional forms used inside (a) displayed as
> ratios; the PER-CELL conditional law for the singleton-residual readings; NO mass
> reading for the (O3) scalings — they exceed 1); clauses (b)/(d): statements about
> the one-step strata of the C_e-conditional process; clause (c): the per-visit
> margin sub-clauses CONDITIONAL on the block state law C_e (the loop/exit masses
> and the (r1) margins are C_e-conditional probabilities), and the per-block
> a.s.-exit sub-clause a statement about the C_μ-conditional law of each block μ —
> [REVISION 2, review advisory 7: "per sub-clause as displayed" was not itself a
> scope statement; the two sub-clauses' reference measures are now named]:

**Proof obligations.** No new mathematics. ONE r4 duty [REVISION 2, advisory 7]:
sweep every downstream occurrence of the unqualified word "mass" in the leaf (§§3–7)
and pin each to its clause-(a)/(a′) reference measure or reword — the "obligations:
none" of REVISION 1 was too strong until that sweep is on file. Survives verbatim:
all (a) bullets, (b)'s one-step content, (c), (d), M1′.

### 2.2 C2 — the family-(v) L6a cell factor (the relaxed-box event)

**Defect.** (a′) claimed each q^{−b} occurrence "IS the Haar mass of the displayed
valuation box it names there — e.g. … the L6a cell factors q₀^{−N(P)}", but the cell
mass is (1−q₀^{−1})^k·q₀^{−N(P)} and NO valuation-box event was defined: the same
factor-as-mass inference the revision had withdrawn for general factors.

**Why a true-scope repair exists (checked against the VERIFIED O-12 brief in this
design).** L6a's verified display (O12_phaseB_verifybrief_rev4.md, "L6a (cell
identification and volume)") gives the cell as a PER-COORDINATE valuation event:

> { g : v(a_{e−i}) ≥ ⌈h_i⌉ for EVERY column i ∈ {0,…,e−1}, with equality
>   v(a_{e−x_j}) = h_{x_j} at the k vertex columns },  volume (1−q₀^{−1})^k·q₀^{−N(P)},
>   N(P) := Σ_{i} ⌈h_i⌉,

and its proof displays P(v ≥ t) = q₀^{−t}, P(v = t) = (1−q₀^{−1})q₀^{−t} per
independent coordinate. So the box is already displayed as the ≥-part of L6a's own
event description; only its NAME and one two-line lemma are missing.

**NEW DEFINITION + LEMMA (verbatim, into the r4 text at (a′)).**

> **Definition (relaxed box).** For an L6a polygon cell — by L6a's verified display,
> {g : v(a_{e−i}) ≥ ⌈h_i⌉ for every column i, with equality at the k vertex columns}
> — its RELAXED BOX is □(P) := {g : v(a_{e−i}) ≥ ⌈h_i⌉ for every column i} (the k
> equalities relaxed to the inequalities L6a already displays; cell ⊆ □(P)).
>
> **Lemma (BOX-VOL).** vol(□(P)) = q₀^{−N(P)} with N(P) = Σ_i ⌈h_i⌉ (L6a's own
> exponent), and P(cell | □(P)) = (1 − q₀^{−1})^k; hence L6a's cell mass factorizes
> as P(cell) = P(cell | □(P)) · vol(□(P)) with BOTH factors masses/conditional masses
> of displayed events.
> *Proof.* The coefficient coordinates are independent Haar with P(v ≥ t) = q₀^{−t}
> and P(v = t | v ≥ t) = 1 − q₀^{−1} — the two per-coordinate computations displayed
> inside L6a's verified proof; □(P) imposes one ≥-condition per column; the cell
> additionally one equality per vertex column; multiply over the independent
> coordinates. ∎

**REPAIRED (a′) FIRST SUBLIST (verbatim; replaces the q^{−b} bullet).**

> * q^{−b} (0 ≤ b ≤ E_n): each occurrence IS the AMBIENT Haar mass of a displayed
>   valuation box — vol(C_e) = q₀^{−e} (box {v(a_i) ≥ 1 ∀i}), vol(R_e) = q₀^{−E}
>   (box {v(a_i) ≥ i ∀i}) [L1]; the conditional form used inside (a) is the displayed
>   ratio P(R_e | C_e) = q₀^{−(E−e)}; and each L6a cell factor q₀^{−N(P)} IS
>   vol(□(P)), the ambient mass of the cell's relaxed box, with cofactor
>   (1 − q₀^{−1})^k = P(cell | □(P)) [Definition + Lemma (BOX-VOL) above].

**Fallback (only if the plan-review rejects (BOX-VOL)'s L6a reading).** Narrow the
sublist to the C_e/R_e occurrences and withdraw the per-factor claim at L6a cell
factors entirely (mass reading only through the full cell mass at (a)'s polygon
bullet). §4 shows NO downstream need consumes the per-factor reading, so the fallback
costs nothing on the mandatory path.

### 2.3 C3 — the §5/§7 billing contradiction (display repair)

**Defect.** (a′) correctly admits the (O3) scalings q^{E_m}/(q^{E_m}−1) are "NOT
masses (they exceed 1)", yet §5 clause 1 bills "PROVED … family (v) per entry per
(a′)" and §7 bills the unit charge "covered exactly at (a)/(a′)/M1′".

**REPAIRED BILLING (verbatim replacement lines).** §5 clause 1's family-(v) fragment
becomes:

> family (v): the q^{−b} occurrences (ambient box masses, incl. the relaxed-box
> reading of the L6a factor) and the (q^d−q^{d−1})^{−1} occurrences (per-cell
> singleton-residual conditional masses) per entry per (a′); the (O3) scalings are
> NOT masses — their entire mass content is (a)'s (O3) bullet (scaling × exit mass =
> mass of the displayed resummed event), and they are billed ONLY so;

and §7's coverage sentence becomes:

> The unit charge's "kernel/entry VALUES are masses" is covered exactly at (a)
> (families (i)–(iii), per entry, conditional on C_e), at (a′)'s box and
> singleton-residual readings, and at M1′'s concrete recorded row; it is NOT covered
> per entry at the (O3) scalings (only their products with exit masses are event
> masses), and families (iv)-arbitrary-α/(vi)/(vii) + the (S3) weight are excluded
> ((a″)).

### 2.4 C4 — M1(b)'s multi-step disjointness (prefix-free restriction + the grammar fact)

**Defect.** "Multi-step events built from disjoint strata by the step maps are
disjoint at the first differing step" is FALSE: with w a proper prefix of w′,
E_{w′} ⊆ E_w (the verifier's loop-0 / loop-0-then-exit counterexample).

**REPAIRED CLAUSE (verbatim; replaces the refuted sentence inside (b)).**

> **(b-PF) [prefix-free multi-step disjointness].** For a finite word
> w = (s_1, …, s_k) over the one-step strata let E_w := {step j lies in s_j,
> j = 1..k} (composed through the step maps). If W is PREFIX-FREE — no member is a
> proper prefix of another — then {E_w : w ∈ W} is pairwise disjoint: two distinct
> members first differ at a position j that both words reach; on the common prefix
> the composed step-j state is the same point, and the one-step strata are pairwise
> disjoint at it by (b)'s one-step clause. [Without prefix-freeness the claim is
> FALSE — E_{w′} ⊆ E_w whenever w is a proper prefix of w′; the rev-3 sentence is
> WITHDRAWN at that generality.]
>
> **(b-EX) [grammar exhaustiveness — an OPEN LEMMA and a D-11 r4 PROOF OBLIGATION;
> REVISION 2: the rev-1 "(b-SW)" presented this as "a FACT of the displayed
> grammar", which the plan-review correctly rejected — the seven-family enumeration
> does not by itself demonstrate the exhaustiveness claim; it must be PROVED by a
> grammar induction].** Every within-block multi-step continuation event booked by a
> row of the DISPLAYED 𝔅_n row families (i)–(vii) (O-12 §2.3: E(e) IS the union of
> those seven displayed families), under any of the three displayed booking
> adjustments (§2.3(iv)/§2.4: the (O2) α-fold, the (O2′) re-feed leg, the (O3)
> scaling), is indexed by a set of STOPPING WORDS over the one-step strata — words
> whose proper prefixes are all-(loop-0) and whose final letter is not (loop-0).
> Any set of stopping words is prefix-free (a proper prefix of a stopping word is
> all-(loop-0), and no stopping word is all-(loop-0)), so (b-PF) applies to every
> such family. [Concrete packs' combined/adjusted rows remain clause-4 content —
> the existing scope sentence stands unchanged; (b-EX) quantifies over the DISPLAYED
> grammar only.]

**Proof route for (b-EX) — the grammar induction the r4 must write out, sketched
here case-by-case (the sketch is possible because the leaf's consumed §grammar,
O-12 §2.3, DEFINES E(e) as the union of the displayed families (i)–(vii) and §2.4
displays exactly three booking adjustments, so the case enumeration below is
exhaustive over the displayed grammar BY CONSTRUCTION of E(e)):**
* family (i), kernels: (O1)/(O2)/(O2′) book one-step unions of loop strata — no
  multi-step content; (O3) books E_rec = {(loop-0)^{L−1}·(loop-c, c ≠ 0) : L ≥ 1} —
  stopping words. [In family (i) the only (g4) closure running along the TIME axis
  is the (O3) resummation, displayed as Σ_{w≥0} q^{−Ew}·(q−1)q^{−E}.]
* family (ii), divisor-pattern masses: one-step strata (patt-π). No word structure.
* family (iii), polygon-family masses: one-step strata (poly-κρ⃗); their (g4)
  closures (exponents c_j ≥ 1) run along the DEPTH axis w of L6b's cone — countably
  many CELLS of the SAME step (O-12 §2.2 lists the polygon strata among the
  one-step strata of C_e \ R_e), never a second step of 𝒟_e.
* family (iv), verdict rows: each books its exit stratum F — one-step at block e
  (the children cross into blocks μ < e: hand-off content consumed at M2's layer
  through (S1)/(S2), not an M1(b) multi-step event); the (O2) α-adjustment books
  the one-step recentering mass; the (O2′) re-feed leg books the one-step
  recentering strata; the (O3) adjustment scales each exit row to
  {(loop-0)^L ∘ F : L ≥ 0} — stopping words.
* family (v), scalar atoms: book no events except through their occurrences inside
  (a)/(a′) and the (O3) exit scalings — the latter exactly family (iv)'s (O3) case.
* families (vi)/(vii), β-legs and solved entries: book NO block-e continuation
  events ((a″) excludes them from every mass claim; their density reading is
  Theorem M2's conditional conclusion).
The r4 write-out = this case check stated against the displayed definitions, one
paragraph per family. Honesty clause: if any case fails to close from displayed
text at the r4 pass, (b-EX) stays an OPEN lemma at the failing family, every
consumer citing it inherits that conditionality, and §4's N1 re-opens — the
outcome is priced in advance, not assumed away.

**(LOOP-∞) [the infinite loop-0 word — handled SEPARATELY; REVISION 2, review
finding 2: it is not a finite word and is outside (b-PF) as stated].** Set
{loop-0 forever} := ⋂_{L≥1} {first L steps = (loop-0)} — measurable (a countable
intersection of composed preimages of displayed strata under the step maps).
(i) NULL: its C_e-conditional mass is ≤ P(first L steps = (loop-0) | C_e) = κ₀^L =
q₀^{−EL} → 0 (the Markov property, L2+L3, as in M1(c)'s per-block clause — here at
the single stratum (loop-0)). (ii) DISJOINT from every finite stopping-word event
E_w: the word w's final letter, at position |w|, is NOT (loop-0), while on
{loop-0 forever} step |w| lies in (loop-0); both events constrain step |w| through
the same composed step maps, and the one-step strata at the composed state are
pairwise disjoint by (b)'s one-step clause — so E_w ∩ {loop-0 forever} = ∅. Hence
(c)'s complement reread decomposes the loop region EXACTLY as
⨆_{stopping words w} E_w ⊔ {loop-0 forever}, the last term null — the
countable-additivity computations of (a)'s (O3) bullet are unaffected.

**WHERE prefix-freeness is discharged for the consumed row-walks [REVISION 2 — no
longer claimed as a no-hypothesis grammar fact]: at (b-PF) (argued above) + (b-EX)
(r4 proof obligation, route displayed) + (LOOP-∞) (displayed argument).** Consumers
re-pointed in r4: (a)'s (O3) bullet ("pairwise disjoint (they differ at the first
non-(loop-0) step)" → "pairwise disjoint by (b-PF), the family being stopping words
per (b-EX)"), the (O3) exit-scaling line, (c)'s complement reread (→ (LOOP-∞)), and
M2's renewal-equation exhaustiveness note (which cites M1(b)/(d)).

**Proof obligations.** (b-PF): the two-sentence argument displayed above (the
composed-state observation is the only content; it is the same measurable-preimage
reading already used in §1). (b-EX): the r4 grammar-induction write-out per the
displayed route — an OPEN LEMMA until it lands AND passes the r4 hostile pass.
(LOOP-∞): the two-part display above, transcribed. Everything else in (b) survives
verbatim.

### 2.5 G8 — M3(a)'s "EVERY polynomial" (separable-scope restatement)

**Defect.** The consumed premise (O5triple Theorem E) covers "every monic SEPARABLE
lift"; M3(a) concluded "the true type of EVERY polynomial of the event's cylinders" —
separability of every lift is not displayed (ns-null justifies only a.e.).

**REPAIR (verbatim; the conclusion sentence of M3(a)).**

> So the verdict σ labeling a decided continuation/termination event is the true
> splitting type of EVERY MONIC SEPARABLE polynomial of the event's cylinders — lift
> uniformity per box at Theorem E's own scope. Mass-sufficiency note: the
> nonseparable locus is Haar-null (T-6 (ns-null), VERIFIED-DUAL), so every
> mass/counting consumption of these labels (Step 18's K1/K4 interfaces) is
> unaffected; pointwise all-lifts separability at a counted box is NOT claimed here —
> where a counting consumer needs it, it is supplied by that consumer's own
> decided-ns-free certificate apparatus (O-1thr §1.4's fiber clauses; D-15's
> vocabulary), not by this clause.

**The consumer-side check (REVISION 2, review finding 3 — EXECUTED for this
revision; sources read in full for it: O-1thr `O1thr_phaseB_verifybrief_rev4.md`
§1.4 (states/trees/fibers: the "decided ns-free" definition and the fiber clauses
(F1)–(F6)) + §6 Theorem 3 (= D-15, incl. the displayed count definition D_σ(N));
M04 `M04-series-tie_fable.md` §§2–5 (Theorems 1–2, Lemma 3.3, Theorem 4 = the
K1–K4 reduction); ROOT Step 18's K1/K4 lines and the Step 11/12 → Step 17 label
route).** The review's question: does every Step-18 K1 box receiving an M3 label
carry a decided-ns-free certificate — EXACT classification, not a.e.? The answer
is YES, by the displayed DEFINITIONS of the counted corpus, and REVISION 2
displays it as a lemma with its warrant (r4/r11 carry it per §7 E9):

> **Lemma (K1-NSF) [every labeled K1 box carries the decided-ns-free
> certificate].** Every box that receives a verdict label anywhere in Step 18's
> K1/K4 chain fibers a decided NS-FREE tree T — i.e. carries the full certificate
> fiber(T, x) = (F1)–(F6) with T decided ns-free — and D-15's exact-classification
> package (fiber = EXACT finite union of level-thr(T) cylinders; the exact count
> tie #Φ_N(T) = mass(T)·p^{nN}; per-box uniqueness/disjointness) applies to it
> with NO a.e. weakening. *Warrant (definitional unfolding of displayed text, no
> new mathematics):* (w1) O-1thr §1.4 defines the ONE bundled predicate "decided
> ns-free := every maximal chain is a (τ-irr) leaf and the Hensel payload covers
> the simple part — no ns-marks"; an ns-halt (τ-ns) is a MARKED halt that is not
> a (τ-irr) leaf, so there is no decided-but-ns-marked class in the displayed
> vocabulary to leak through. (w2) O-1thr Theorem 3(c) defines the level-N
> decided-σ count D_σ(N) := #{x level-N : fiber(T, x) for some DECIDED NS-FREE T
> with typemult = σ} — the corpus is decided-ns-free-quantified in its displayed
> definition. (w3) M04 Theorem 2(a)'s partition (Σ_σ decided_σ(N) + undec(N) =
> p^{nN}, the verdict map f ↦ canonical N f) routes every box whose canonical run
> is not decided — in particular every ns-halted box — into the NONE-fiber
> undec(N): such boxes receive NO label. (w4) K1/K4's corpus ("complete finite
> realizable canonical trees"; bridgeMass at decided trees, with (ns-null)
> excluding infinite trees) is keyed to the SAME decided corpus that the
> count_tie/finiteness_stack interface ties to D_σ(N) — the corpus KEYING is
> definitional on both sides; the numerical tie itself is the count_tie row's
> content, priced at its own home, not consumed by this lemma. ∎

**The two consumption channels (what M3 does and does not supply at K1 —
displayed so the a.e./exact distinction cannot blur again):**
* **(ch-1) K1's EXACT combinatorics** — the cylinder classification, the
  finite-level counts, Lemma 3.3's weight-preserving regrouping — consumes D-15 +
  the K1 kernels AT decided ns-free trees and is LABEL-SEMANTICS-BLIND: both
  sides are keyed by the trees' RECORDED verdict multisets; no statement on this
  channel reads the true type of any polynomial. M3 is not consumed here, so its
  separable-lift scope cannot injure the exact content.
* **(ch-2) the SEMANTIC tie** (recorded labels = true types) — where M3(a)
  enters (via Steps 11/12 → Step 17): consumed MASS-MEDIATED. Each counted box's
  true-σ locus is the box minus its nonseparable locus (M3(a) at separable scope,
  applicable by Lemma (K1-NSF)), of full box mass by T-6 (ns-null) — exactly what
  the Step-19 squeeze and Step 18b's density reading consume. No mandatory
  consumer reads a true type at an individual nonseparable lift.

**Contingency (NS-ALL), still flagged not priced — NARROWED by the executed
check:** it fires only if a verification pass finds a consumer needing all-lifts
separability FROM M3 at boxes not definitionally ns-free — i.e. a consumer
OUTSIDE both displayed channels; the REVISION-2 check found none on the
Step-17/18/18b/19 path. If one is found, (NS-ALL) is priced as an explicit open
lemma per §6.

### 2.6 G9 — the falsifier-criterion display

§6's "every entry defined with value in [0, 1] (necessary for M1(a))" and the "single
failure — an entry outside [0, 1] … would have refuted M1(a)" sentence are rescoped
(display only): the [0,1] criterion is necessary for M1(a) exactly at families
(i)/(ii)/(iii) (the (a″) scope); the (O3) scaling entries are checked against their
displayed > 1 form; an out-of-[0,1] value at a family-(i)–(iii) entry would have
refuted M1(a). No scanned quantity changes (the scan already keys entries by family).

### 2.7 C7 — M3(b)'s silent clause-4 consumption (leaf hygiene; ROOT already insulated)

The impact audit graded C7 INSULATED: ROOT's Step 17 REVISION-4 note + the §3.2 D-11
[V] row already price the actual-pack correspondence as (H5), so ROOT assumes what
the leaf sentence hid. The LEAF sentence is still false as written. **REPAIR
(in-statement conditionality, verbatim):** M3(b)'s first sentence becomes

> Under the clause-4 correspondence (OPEN — §5 clause 4 = OL-O12-2's data half;
> ROOT prices it as (H5)/(PACK)), M1/M2's identities attach to the ACTUAL tables'
> values; unconditionally, M1/M2 identify entries of a stipulated 𝔅_n member and the
> displayed (R-read) with masses of SEMANTIC strata (root valuations, reductions of
> rescales, Newton polygons, residual shapes) — and this clause ties those semantic
> strata to the classifier vocabulary:

with the rest of M3(b) (the GD/CU dictionary and its displayed conditionality)
byte-stable.

---

## 3. LAYER M2 (consumed at ROOT Step 18b): the (RE) true-scope repair, with a priced fallback

### 3.1 The finding, restated precisely

M2 as displayed: "Assume (S1) and (S2) for the member. Then … the abstract solved
values ARE the real conditional densities" — quantified over ALL 𝔅_n members. The
verifier's counterexample: 𝔅_n admits members with ARBITRARY allocation data α_e
(rows can leave [0,1]) while (S1)/(S2) still hold; and the proof's step "With M1(a)
(each P(F) is the abstract mass entry at q₀)" mis-cites M1(a), which the r3 rescoped
to families (i)–(iii) — family-(iv) verdict rows are excluded. The impact audit
gestured at a "semantic verdict-row allocation premise" as the missing hypothesis.

### 3.2 The decisive grammar facts (checked against the VERIFIED O-12 brief for this design)

From `O12_phaseB_verifybrief_rev4.md` §2.3(iv) (verbatim, verified text):

> The verdict row of F at verdict σ is row_σ(F) := m(F) · Σ_{comp_F(σ⃗)=σ}
> ∏_i β_{μ_i}(σ_i)(q^{D_i}), a finite sum of products with coefficients 0 or 1 — no
> other scalars enter. … Booking adjustments (§2.4): under (O2) the table carries one
> further datum, the *allocation datum* α_e … and the aggregated verdict row becomes
> t_σ + α_e(σ)·q^{−E} …; under (O3) every exit row is multiplied by the scaling
> q^E/(q^E−1) of family (v).

and §1:

> the machine-checked degree-2 table = (O2) at n = 2; the sealed degree-3 tables =
> (O3); the general-n engine = (O1).

Consequences: **(g-i)** in 𝔅_n's own grammar, family-(iv) verdict rows are the
CANONICAL 0/1-coefficient semantic assembly BY DEFINITION; **(g-ii)** the arbitrary
allocation datum α_e exists ONLY at the (O2) booking; **(g-iii)** the (O2′)
adjustment is the pinned re-feed leg κ₁·x (coefficient = κ₁ exactly, per the §2.4
display M2 already quotes), and the (O3) adjustment is the deterministic family-(v)
scaling — neither introduces free scalars; **(g-iv)** the intended density-carrying
instances are (O1) (general n) and (O3) (sealed n = 3), never (O2) — D-11's M1′
already pins this ("the instance pin's target must be (and is) the re-entrant
bookings"), and M1′ moreover shows NO α-constraint could rescue M2 at (O2): the (O2)
booking's solved values differ from the true densities even with the semantic
α₂ = (0, q−1), because the booked event is not verdict-constant. So the audit's
gestured "semantic-allocation premise", read as a constraint on α, would be BOTH too
weak (fails at (O2) anyway) and unnecessary (no α exists at re-entrant bookings). The
sound repair is a BOOKING-PROFILE hypothesis.

### 3.3 REPAIRED THEOREM M2 (verbatim)

> **Theorem M2 (r4).** Let the member satisfy:
> **(RE) [re-entrant booking profile].** EVERY block e ∈ {2, …, n} of the member is
> booked (O1), (O2′), or (O3) — never (O2); equivalently (O-12 §2.3(iv)/§2.4) the
> member carries NO allocation datum at any block, so by the displayed grammar its
> family-(iv) verdict rows at every block are the canonical 0/1-coefficient assembly
> row_σ(F) = m(F)·Σ_{comp_F(σ⃗)=σ} ∏_i β_{μ_i}(σ_i)(q^{D_i}), aggregated
> t_σ = Σ_F row_σ(F), with the only booking adjustments the (O2′) re-feed leg κ₁·x
> (coefficient pinned = κ₁) and the (O3) exit-row scaling q^{E}/(q^{E}−1).
> [Arbitrary-α members are EXCLUDED — they are exactly M1(a″)/M1′'s exclusion, and
> for them only O-12's pole/zero theorem speaks; the (O2) member is a gate object,
> not a density carrier (M1′).]
> Assume further (S1) and (S2) for the member. Then for every prime power q₀ = p^δ
> and every block e: β_e(σ)(q₀) = P(splitting type = σ | the block-e state law at
> q₀) for all σ; and the top-layer assembly (root read + entrance weights)
> identifies the solved final densities with the true unconditional splitting-type
> densities of Haar-random monic degree-n f over O. [MONIC scope; the PROJECTIVE
> reading additionally conditional on (S3). The identified top object is the
> DISPLAYED root read (R-read); that a concrete pack's rows equal the member's is
> clause-4 content ((H5)), NOT claimed here — unchanged from r3.]

**REPAIRED PROOF STEP (verbatim; replaces "With M1(a) (each P(F) is the abstract
mass entry at q₀), the semantic one-step identity is therefore").**

> By (RE) and the verified grammar display (O-12 §2.3(iv), quoted in §0), the
> member's exit/verdict rows at block e are the canonical assembly: each exit
> stratum F contributes m(F) times the 0/1 comp_F-selected products of β-legs, with
> no other scalars. By M1(a) (families (ii)/(iii) — in scope after the r3 rescope),
> each m(F)(q₀) = P(F | C_e). By (S1)+(S2), P(type σ | F) =
> Σ_{comp_F(σ⃗)=σ} ∏_i β*_{μ_i}(σ_i at q₀^{D_i}), and by the induction hypothesis
> (every lower block is also re-entrant-booked under (RE)) each β*_{μ_i}(· at
> q₀^{D_i}) = β_{μ_i}(·)(q₀^{D_i}). Hence the member's abstract exit row equals the
> true exit row: s_member(q₀) = s_true(q₀), and the semantic one-step identity is
> the member's balance equation:

with the three displayed booking legs ((O1)/(O2′)/(O3)) and the uniqueness-pivot
close byte-stable. The r3 note that exhaustiveness consumes M1(b)/(d) is re-pointed
to (b)/(b-PF)/(b-SW) per §2.4.

**At the CONSUMED instance: the definitional discharge is WITHDRAWN [REVISION 2,
review finding 1] — (RE)+row-form at the consumed member is (PACK-iv), a NEW [M]
member of (H5); §3.5 is now the PRIMARY route.** REVISION 1 claimed (RE) at the
member ROOT consumes rides the "on-file instance pin" (O-12 §1: "the sealed
degree-3 tables = (O3); the general-n engine = (O1)"; D-11 M1′). The review refuted
the warrant, and the refutation is ACCEPTED on re-reading the quoted text itself —
the reasons, recorded so the withdrawal is durable:
* the O-12 §1 sentence names the project's concrete tables' INTENDED bookings, but
  O-12's own scope declaration (§1, verbatim) makes the identification of the
  COMPLETE sealed degree-3 tables with an (O3) member "an interface assumption
  declared outside this proof (recorded as the labeled open item OL-O12-2)", and
  the general-n identification likewise ("declared outside this proof, NOT proved
  here and NOT part of the claim"). So the quoted sentence cannot pin the
  PER-BLOCK BOOKING PROFILE of the member ROOT actually consumes: that member is
  reached only through (H5), and its booking profile is exactly (H5)-class
  content — hypothesis, not verified text;
* absence-of-α does not prove the profile: the §2.3(iv)/§2.4 displays establish
  that the allocation datum exists only under (O2) — i.e. (O2) ⟹ carries α — NOT
  the converse; and (RE) needs more than "no α": every block booked
  (O1)/(O2′)/(O3) AND the family-(iv) rows equal to the canonical 0/1-coefficient
  assembly with only the displayed adjustments — a per-block booking + row-form
  profile that no quoted display pins for the consumed member;
* M1′'s "instance pin" is a sentence of D-11's own repaired chain — an assertion
  inside the artifact under repair, not independent evidence of pack-to-member
  conformance.
The grammar facts (g-i)–(g-iv) above remain correct AND load-bearing — but in two
demoted roles only: as the derivation "(RE)-member ⟹ canonical verdict rows"
INSIDE Theorem M2 (r4) (a theorem about members satisfying (RE), honest as
stated), and as (PACK-iv)'s RETIREMENT ROUTE (next paragraph) — never as a
discharge at the consumed instance. The concrete pack's conformance to the member
remains (H5)'s correspondence clause, unchanged. ROOT r11 displays the PRICE at
Step 18b (§7, edit E3) and adds (PACK-iv) to the (H5) row as a NEW hypothesis
member (edit E4 — worded as an ADDITION to the row-law roster, never a
clarification).

**(PACK-iv)'s RETIREMENT ROUTE — what would discharge it later (the surviving
content of the withdrawn analysis, kept per the revision charge).** (PACK-iv)
retires when the booking profile and row forms of a consumed member become
VERIFIED DATA rather than hypothesis:
* (route-a), n = 3: the OL-O12-2 transcription-and-correspondence pass (D-11 §5
  clause 4's data half), EXTENDED BY ONE NAMED DUTY — per sealed row, verify the
  block's booking against the (O3) forms and the row against §2.3(iv)'s canonical
  assembly + the displayed (O3) scaling. (Finite data comparison, the same
  execution class as before; naming the duty prevents the pass from silently
  skipping the booking-profile half.)
* (route-b), general n: the O-14d instance population constructing the member IN
  the (O1) booking — the profile then holds BY CONSTRUCTION and is checkable at
  population time.
On either route's verified completion at a consumed instance, (g-i)–(g-iv)
convert "verified re-entrant profile, no α" into the canonical row-form clause BY
the displayed §2.3(iv) definition, and (PACK-iv) retires into the executed
correspondence at that instance.

**Proof obligations for M2 r4:** (RE)-grammar cite displayed (quote §2.3(iv) into
the leaf's §0 consumed-inputs list — it is brief-internal displayed content of the
VERIFIED leaf, same class as the §2.4 booking displays already consumed); the
repaired proof step above; everything else in M2's proof survives verbatim (the
(O2′)/(O3) legs, the Theorem 1(3) fold, the pivot, the root layer).

### 3.4 G5 — Lemma M2.0's address induction (loop-extended addresses)

**Defect.** Addresses recorded only (hand-off stratum, child slot) pairs, but a
child is born after L ≥ 0 within-block loop steps then exit through F; the induction
step "{node a reached} = {node a′ reached} ∩ {x_{a′} ∈ F}" is false when loops
precede the hand-off (reaching the child is a countable union over loop words).

**REPAIR (structure, to be written out in r4 at the displayed level of the current
step 3).** (i) Addresses become a = ((w_1, F_1, i_1), …, (w_k, F_k, i_k)) with w_j a
finite WORD over block-level j's loop strata (executed before the j-th hand-off) —
still countable (finite words over a finite loop alphabet per block: loop-0 and the
q₀−1 recenterings; countably many polygon cells for the F's as before). (ii) The
≪-transport induction runs over ONE LETTER at a time, with two letter kinds:
LOOP letters — the pushforward of the normalized restriction of Haar-C_e to a loop
stratum s under the loop step map IS Haar-C_e: verbatim L2+L3 ("conditioned on the
stratum, ĥ is AGAIN the state law"), PROVED, no seam; HAND-OFF letters — (S1-m), as
now. The kernel-null-set step is unchanged in form at both letter kinds. (iii) Step
2's reduction sentence gains "after executing its finite loop word" at the node-birth
reading.

**The r4 OBLIGATION LIST for the rewritten Lemma M2.0 [REVISION 2, review finding
5 — the facts the loop-extension must PROVE, not assert; each with its displayed
route; §4's N4 rests on exactly these]:**
* **(O-1) [the child-reached identity — the disjoint/countable-union display].**
  For a node a′ and a child slot (F, i): {child (F, i) of a′ reached} =
  ⨆_w ({a′ reached} ∩ {the within-block trajectory at a′ executes the finite loop
  word w, then lands in F}) — a COUNTABLE union, PAIRWISE DISJOINT over the words
  w over block-μ(a′)'s loop alphabet ({loop-0} ∪ {loop-c}_{c≠0}). Route: the
  words w·F are stopping words in the generalized sense (proper prefixes all-loop,
  final letter the exit stratum F); pairwise disjointness at the first differing
  position is (b-PF) — (b)'s one-step clause covers the full mixed loop alphabet;
  countability: finite words over a finite-per-length alphabet; exhaustion of
  {child reached} minus the (O-2) null set: under (DET) the trajectory is a
  deterministic map sequence, so reaching the child MEANS some finite loop history
  precedes the hand-off. This identity REPLACES the rev-3 false one-letter
  induction equation {node a reached} = {node a′ reached} ∩ {x_{a′} ∈ F}.
* **(O-2) [the infinite pre-hand-off loop path].** At every node a′ with
  P(a′ reached) > 0: P(the within-block trajectory at a′ never exits | a′ reached)
  = 0. Route: the eternal-loop set N_μ ⊆ C_μ is Haar-null (M1(c)'s per-block
  clause, over ALL loop strata); the reached-conditioned law of x_{a′} is ≪
  Haar-C_μ (the step-3 induction); null pulls back to null.
* **(O-3) [measurability of the iterated restrictions and maps].** Every loop
  letter's step map (g ↦ ĥ = h(c̃ + y) on its stratum) is measurable; finite
  compositions along a word are measurable; every event in (O-1)/(O-2) is a
  composed preimage of displayed strata — the L2/L3/L6 measurability layer of §1,
  applied finitely often per word; the r4 writes the composition sentence once,
  at the loop-extended addresses.
* **(O-4) [preservation of normalized conditional laws after arbitrary loop
  words].** Under the CANONICAL block law, conditioned on executing the loop word
  w, the post-w state law IS Haar-C_{μ(a′)} exactly (|w|-fold L2+L3, each letter's
  normalized stratum restriction pushing forward TO the state law); under a
  reached-conditioned law that is merely ≪ Haar-C_{μ(a′)}, absolute continuity is
  preserved letter-by-letter (the kernel-null-set step with (S1-m) replaced by the
  PROVED L2+L3 statement). This is the loop case of the two-letter transport and
  the exact reason the billing does not widen.
* **(O-5) [where per-block a.s. exit is consumed — the explicit discard of
  infinite words].** The address-tree accounting uses (O-2) at EVERY node so that
  {a′ reached} = ⨆_w {a′ reached, w then exit through some (F, i)} ⊔ (null) loses
  no mass; the r4 displays this consumption line explicitly at the induction step
  (it is where M1(c)'s per-block bound, transported by ≪, is spent).

**Billing: (S1-m) + (DET), claimed UNCHANGED — but demoted at REVISION 2 from an
established fact to the design-level claim the r4 proof must bear out** ((O-4)'s
loop legs consume only the PROVED L2/L3; (O-1)/(O-3) are structural; (O-2)/(O-5)
consume M1(c) + the ≪-induction). The honest-widening paragraph ((S1-m+) under a
stochastic hand-off reading) survives verbatim. Until the (O-1)–(O-5) write-outs
land AND pass the r4 hostile pass, Lemma M2.0 stands REPAIR-DESIGNED, not
repaired (§4 N4).

### 3.5 (PACK-iv) — the PRIMARY route's [M] member [REVISION 2: PROMOTED from
fallback — the plan-review ruled §3.3's grammar/pin discharge unwarranted (its
finding 1), and the ruling is accepted with the reasons recorded at §3.3]

The priced form is the following NEW (H5) clause, stated per the PACK-i/ii/iii
genre AT the 𝔅_n member. E4 presents it as a NEW HYPOTHESIS MEMBER — an
enlargement of (H5)'s displayed row-law roster, exactly the mechanism by which
PACK-i/ii/iii entered at ROOT REVISION 7 — NEVER as a clarification of existing
content (review finding 1's closing charge):

> **(PACK-iv) sem_alloc — semantic verdict-row form at the intended member.** At
> every block e of the intended 𝔅_n instantiation, the booking is re-entrant
> ((O1)/(O2′)/(O3)) and the family-(iv) source/verdict rows are the canonical
> semantic assembly: every verdict-row entry equals
> Σ_{F exit} m(F)·Σ_{comp_F(σ⃗)=σ} ∏_i β_{μ_i}(σ_i)(q^{D_i}) — plus, at (O2′), the
> displayed κ₁ re-feed leg and, at (O3), the displayed family-(v) exit scaling, and
> nothing else — with m(F) the member's family-(ii)/(iii) mass entry and the β's its
> family-(vi) legs; the member carries no allocation adjustment beyond these. [The
> premise D-11 r4's Theorem M2 names as (RE); (S1)/(S2) do NOT imply it (owed-pass
> C6); consumed at Step 18b ONLY — Step 18's K2/K3 glue consumes PACK-i/ii/iii, and
> Step 17's M1 excludes family (iv) in-statement ((a″)).]

**One-home argument (why (H5) enlargement, not a new row):** (H5) is BY
CONSTRUCTION "the actual-pack correspondence PLUS the pack row-laws … stated AT THE
𝔅_n ROWS" (REVISION-7 enlargement, finding VC7-2); (PACK-iv) is a row-law at the
𝔅_n rows, same owners (D-11/O-12 with the O-14d pack construction), same consumption
chain (Steps 17 → 18/18b), same borderline-[M]/[T]-kept-[M] disposition (a finite
per-n row-form comparison, RESUM-n3's transcription its executed n = 3 instance). A
separate row would split the 𝔅_n row-law content across two homes against the
VC7-2 precedent.

**[M] accounting [REVISION 2 — exact, per the revision charge]:** (PACK-iv) adds a
MEMBER to (H5), not a row. The §3.1 ROW count after r11 remains ELEVEN — (H8) is
the only new row (§5.1's ten → eleven stands); (H5)'s displayed row-law roster
grows THREE → FOUR (PACK-i/ii/iii → PACK-i/ii/iii/iv, plus the correspondence
clause it always carried). Its named retirement route is §3.3's (route-a)/(route-b)
— content that can retire independently, displayed on the row per the (H8)
precedent.

---

## 4. THE NEED CHECK (decisive): what Steps 17/18b actually need, met need-by-need

**The consumed lines, quoted from ROOT REVISION 9.**

Step 17 Delivers: "the pack-side mass laws + true row labels that Step 18's K1/K2
consume; D-9k's escape input at the pack; the (r1) uniqueness pivot Step 18b
re-uses." Step 18 consumes (K2 leg): "K2 ← O-12 at 𝔅_n + D-11 PACK SIDE (= Step
17's tranche, never M2) + the (PACK) correspondence-plus-row-laws … PACK-i/ii at
THIS K2 evaluation glue …; (PACK-iii) at K3". Step 18b Statement: "(D-11 M2) for
every type τ: α(n, τ; p) — the Haar density of clause (0) — equals the σ-graded tree
series of T_can; equivalently, the solved values are the real conditional
densities"; its proof line names "(S1) … ← Step 14 …; (S2) = the O-11 composition
datum ← Step 18. (r1) is the uniqueness pivot (Step 17)"; Delivers: "the α = series
identification; with Step 18, the α(n,τ;p) = R_τ(p) evaluation clause of (R)."
Step 19 consumes: "Step 18 delivers series = R_τ (O-11); Step 18b delivers
α = series (D-11 M2); TOGETHER they deliver α = R_τ — neither alone does"; plus "the
pole-free specialization at every prime power (Steps 4 + 5 + 17 …)".

| # | need | met by | verdict |
|---|---|---|---|
| N1 | Step 18 K1/K2 ← "pack-side mass laws": per-row stratum masses at the 𝔅_n member, row Σ = 1, row disjointness (incl. the (O3) resummed rows) | repaired M1(a) families (i)–(iii) (conditional-on-C_e, formulas unchanged) + M1(d) + (b) with (b-PF)/(b-SW) covering exactly the consumed multi-step row grammar; member-row Σ = 1 through the canonical grammar + family-(vi) aggregates at (RE) members (Step 17 display rescoped, edit E1). The K2 glue laws at the CONCRETE pack stay (PACK-i/ii); K3's stays (PACK-iii) — unchanged | **MET** |
| N2 | Step 18 K1 ← "true row labels" (M3 leg, via Steps 11/12) | repaired M3(a) at separable-lift scope + T-6 (ns-null) for every mass/counting consumption; label attachment to ACTUAL tables rides (H5) (C7's insulation, now honest in-leaf too). All-lifts separability at counted boxes is the counting side's decided-ns-free certificate content (O-1thr §1.4), not an M3 delivery | **MET** (contingency NS-ALL flagged, §6) |
| N3 | Step 18b ← "the (r1) uniqueness pivot" | Corollary D margins/pivot — untouched by every finding | **MET** |
| N4 | Step 17's termination delivery ("a.s. termination from the (r1) margins"; D-9k's escape input) | M1(c) per-visit margins at (O1)/(O3) + per-block a.s. exit, unconditional (pass-confirmed, byte-stable); multi-block a.s. termination = Lemma M2.0 at (S1-m)+(DET), repaired per §3.4 with billing unchanged; Step-17 display line rescoped to this split (edit E1) | **MET** |
| N5 | Step 18b → Step 19: α = series at the consumed instance | repaired M2 (r4) at (RE) scope; (RE) discharged at the consumed instance by the on-file instance pin (O-12 §1 + M1′) displayed at Step 18b (edit E3); (S1) ← Step 14, (S2) ← Step 18, pivot ← Step 17 as before; concrete-pack attachment = (H5) as before | **MET — no new [M] on the primary route** |
| N6 | Step 19 ← Step 17's pole-free leg | the (r1)/(r2) margins reread — untouched | **MET** |
| N7 | Step 19's Σ_τ R_τ = 1 | rides α = R_τ at every p (N5) + Step 1 — conditionality unchanged | **MET** |

**BLOCKED: NONE.** No need of Steps 17/18/18b/19 fails under the repairs of §§2–3
plus (H8) (§5.1). If the plan-review overturns §3.3's discharge, N5 is met instead
by the (PACK-iv) fallback (§3.5) — still not blocked, priced.

---

## 5. The two O-11 items

### 5.1 O11-G2 — CUT-WD: NEW [M] row (H8)

**What CUT-WD is.** An open kernel of tree node T-6 consumed inside Step 18's K1
(the M04 Lemma 3.3 regrouping): the shallow-cut decomposition / exhaustive-exclusive
read-ownership statement. O-11 r3 displays its serving map (← O-1thr Theorem 1 =
D-14 read locality + CU-3 coherent nonempty locus) as a correspondence CLAIM, not a
demonstrated implication (its own pass-2 G-1 display); the owed pass verified the
gap ("overlapping ownership, an unowned read, or two different shallow
decompositions" are unexcluded). ROOT displays it nowhere (`rg CUT-WD` = 0 hits).
Under the ledger's own classification rule (the VC5/VC6/F-1 genre walked to
completion at REVISIONS 5–6), an open proposition consumed on clause (R)'s mandatory
path cannot ride an unexecuted adjudication promise: it needs an [M] home.

**NEW ROW (verbatim, §3.1 + (ROOT-C)).**

> **(H8) = (K-CUT) — the shallow-cut decomposition kernel** [NEW row at r11, from
> the O-11 owed-pass G-2]: for every n ≥ 2, every prime p, and every splitting type
> σ of degree n, every complete type-σ canonical tree T admits EXACTLY ONE
> decomposition into a shallow shape Ŝ plus per-branch block derivations
> (D_1, …, D_r) — exhaustive-exclusive read ownership at the first-split cut — and
> the decomposition is weight-preserving, μ(fiber T) = W(Ŝ)·∏_i weight(D_i), as M04
> Lemma 3.3's hypothesis consumes it at Step 18's K1. Status: an OPEN KERNEL of T-6
> (the T-6 row's own naming); the O-11 r3 record's serving map (← D-14 + CU-3) is a
> correspondence CLAIM, not a demonstrated implication (O-11 pass-2 G-1; owed-pass
> G-2). Owner: T-6/O-1thr/CU-3 arc. NAMED RETIREMENT ROUTE: O-11 §8 charge (vi) —
> the adjudication of the serving map against T-6's §T-ASSEMBLY; if that
> adjudication demonstrates the implication from on-file content, this row RETIRES
> into the consuming leaves' [V] debts. Enters Step 18 (K1's Lemma-3.3 regrouping),
> hence clause (R); clause (UB) inherits through the transported chain. NOT
> (0)/(SQ).

**One-home adjudication (why not (H6)/(H7)).** Not (H6): CUT-WD's seam is the
first-split cut inside K1, not the terminal seam, and (H6)'s membership is pinned by
the leaf-#9 interlock. Not an (H7) member: the K1 seam CLASS matches, but the owners
differ (T-6/O-1thr/CU-3 vs (H7)'s O-10/GD-family), (H7)'s membership is pinned as
the F-1-adjudicated PAIR, and CUT-WD carries its OWN named retirement route (charge
(vi)) — content that can retire independently keeps its own home. This mirrors the
F-1 sibling-row reasoning exactly.

**Conforming ROOT edits** (executed at r11, listed at §7 E5): (ROOT-C) hypothesis
list + clause (R)/(UB) attribution lines gain (H8); Step 18's K1-a display names it;
the [M] row count syncs (ten → eleven); §3.4's correspondence table gains the
pointer at its Lemma-3.3 rows.

### 5.2 O11-C1 residue — the n ≥ 2 Lean guard (leaf-side note; no ROOT edit)

ROOT is insulated (its §1 opens "Fix n ≥ 2"; the impact audit's disposition (c)).
Leaf-side dispositions to execute with the next O-11 touch (r4): (i) the advertised
target row in O-11's §"Mathematics" gains the explicit "for every n ≥ 2" quantifier
(matching Theorem O11's proved scope); (ii) the normative Lean row `BK.series_tie`
gains the `2 ≤ n` guard at formalization — recorded now in the §3.3
"Item-27/28 Lean statement repairs" row's territory (PARKED engineering) so the
census carries it; no (ROOT-C) content changes.

---

## 6. Contingencies (labeled; neither is a blocker)

1. **(BOX-VOL) L6a-shape dependence** — RESOLVED IN THIS DESIGN: L6a's verified
   display was checked and quoted (§2.2); the r4 executor's only duty is the verbatim
   cite. Fallback (narrowing) specified at §2.2, costs nothing on the mandatory path.
2. **(NS-ALL)** — fires only if a pass finds a mandatory consumer needing all-lifts
   separability FROM M3(a) (§2.5); then it is priced as an explicit open lemma (home:
   (H6)-adjacent, terminal/label seam — adjudicate at that time). §4 N2 argues no
   current consumer does.
3. **(PACK-iv) fallback** — fires only if the plan-review rejects §3.3's
   definitional-display discharge of (RE); verbatim member + one-home argument at
   §3.5.

---

## 7. Execution plan (after the Codex plan-review ACCEPTS this design)

**Unit A — D-11 r4** (leaf repair; COPY rev 3, edits at finding sites only, every
pass-confirmed passage byte-stable; open with a §0-pre dispositions table mapping
pass-3 findings 1–9 → the §§2–3 repairs): L1 preamble (§2.1) · L2 (a′) first sublist
+ (BOX)/(BOX-VOL) (§2.2) · L3 §5/§7 billing (§2.3) · L4 (b-PF)/(b-SW) + consumer
re-points (§2.4) · L5 Theorem M2 (RE) restatement + proof-step replacement + the
§2.3(iv) grammar quote into §0 (§3.3) · L6 Lemma M2.0 loop-extended addresses (§3.4)
· L7 M3(a) separable scope (§2.5) · L8 M3(b) in-statement conditionality (§2.7) ·
L9 §6 falsifier-criterion display (§2.6). Then the r4 hostile pass (fresh context,
Codex; the D-11 registry bar unchanged).

**Unit B — ROOT r11** (display edits; §§1/7–15 discipline as at prior revisions):
E1 Step 17 statement line → the r4-scoped form: "every family-(i)/(ii)/(iii) solve
entry … IS the Haar mass of its continuation event CONDITIONAL on the block state
law C_e; family-(v) atoms at their per-occurrence (a′) readings (ambient boxes /
per-cell singletons; the (O3) scalings NOT masses); families (iv)/(vi)/(vii)
excluded in-statement ((a″)); Σ = 1 at the displayed one-step strata (M1(d)), member
rows through the canonical grammar at re-entrant members; multi-step disjointness at
prefix-free families ((b-PF)), covering every consumed row by the stopping-word
grammar fact ((b-SW)); per-block a.s. exit unconditional, multi-block at Lemma
M2.0's (S1-m)+(DET) (Step 18b's layer)" ·
E2 Step 17 status line gains the pass-3 CRITICAL record + r4 pointer ·
E3 Step 18b proof line → "the D-11 r4 M2 argument at its (RE) scope — (RE)
discharged at the consumed instance by the instance pin (O-12 §1: general-n = (O1),
sealed n = 3 = (O3); D-11 M1′: density carriers are the re-entrant bookings) — with
(S1) ← Step 14, (S2) ← Step 18, (r1) pivot ← Step 17; the concrete pack's
conformance = (H5)" ·
E4 (H5) row + (ROOT-C)(H5): one sentence — "the correspondence's TARGET member is
re-entrant-booked at every block ((O1)/(O3); the (O2) gate object is not a density
carrier)" [If the fallback fires: instead add (PACK-iv) per §3.5] ·
E5 the (H8) row + all conforming displays (§5.1) ·
E6 §3.4 rows 6(iii)–(ix)+7 and 13: "(M1: entries ARE masses)" pointers re-scoped to
the r4 form ·
E7 §3.2 D-11 [V] row synced to r4 (pass 3 CRITICAL; r4 on file; fresh pass owed) ·
E8 ACCEPTANCE STANDING: counter to ZERO everywhere it is displayed (header, §3.2,
§6, footer, §15); the suspension lifts only on a NEW end-to-end adjudication (two
consecutive clean model-diverse passes on identical text, fresh verifiers).

**Order:** Codex plan-review of THIS file → Unit A → D-11 r4 hostile pass → Unit B →
new VC passes. PROJECT_STATE.md + ledger sync at each unit close.

