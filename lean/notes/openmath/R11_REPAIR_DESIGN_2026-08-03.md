# R11 REPAIR DESIGN (2026-08-03) — restoring the composition after the D-11 owed-pass refutations

**Status of this document: DESIGN ONLY.** No edit to ROOT
(`docs/ROOT_ASSEMBLY_2026-08-02.md`, REVISION 9, a2ad88a) and no edit to the D-11 leaf
(`lean/notes/openmath/D11_massid_phaseB_attempt_rev3.md`, 8a0786c) is made here. This
design goes to a Codex plan-review BEFORE execution; §7 lists the execution units.

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
| D11-C4 (M1(b) disjointness) | TRUE-SCOPE REPAIR | (b-PF) prefix-free lemma + (b-SW) stopping-word grammar fact; prefix-freeness IS a fact of the 𝔅_n row grammar (§2.4) |
| D11-G5 (M2.0 addresses) | TRUE-SCOPE REPAIR | loop-extended addresses; two-letter transport induction (loop letters ← L2/L3 PROVED, hand-off letters ← (S1-m)); billing unchanged (§3.4) |
| D11-C6 (M2 false at scope) | TRUE-SCOPE REPAIR (primary) | hypothesis (RE): all blocks booked re-entrant — then verdict rows are canonical BY THE VERIFIED 𝔅_n GRAMMAR (α exists only at (O2)); (RE) discharged at the consumed instance by the on-file instance pin. FALLBACK [M] member (PACK-iv) drafted verbatim (§3) |
| D11-C7 (M3(b) silent clause 4) | leaf statement hygiene | conditionality moved in-statement; ROOT already insulated at (H5) (§2.7) |
| D11-G8 (M3(a) "EVERY polynomial") | TRUE-SCOPE REPAIR | conclusion at separable lifts (= Theorem E's scope) + ns-null mass-sufficiency note; contingency (NS-ALL) flagged (§2.5) |
| D11-G9 (falsifier criterion) | display repair | criterion rescoped to (a″)'s families (§2.6) |
| O11-G2 (CUT-WD) | [M] PRICE | NEW row **(H8) = (K-CUT)**, with the O-11 charge-(vi) adjudication as named retirement route (§5.1) |
| O11-C1 residue (n ≥ 2 guard) | leaf/Lean note | O-11 r4 restates the target row at n ≥ 2; BK.series_tie carries the guard at formalization (§5.2) |

**BLOCKED list: EMPTY.** Every need of Steps 17/18b is met by the repairs + the one
new [M] row; §4 runs the check need-by-need. Two labeled contingencies (not
blockers) at §6.

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
> the one-step strata of the C_e-conditional process; clause (c): per sub-clause as
> displayed:

**Proof obligations.** None new. Survives verbatim: all (a) bullets, (b)'s one-step
content, (c), (d), M1′.

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
> **(b-SW) [the consumed families are stopping words — a FACT of the displayed 𝔅_n
> row grammar].** Every multi-step continuation event this document books — the (O3)
> kernel's family {E^{(L)}}_{L≥1} (words (loop-0)^{L−1}·(loop-c, c ≠ 0)), each
> (O3)-scaled exit family {(loop-0)^L ∘ F}_{L≥0} (F a fixed exit stratum), and their
> union with {loop-0 forever} in (c)'s complement reread — is indexed by STOPPING
> WORDS: every proper prefix is all-(loop-0) and the final letter is not (loop-0).
> Any set of stopping words is prefix-free: a proper prefix of a stopping word is
> all-(loop-0), and no stopping word is all-(loop-0). So (b-PF) applies to every
> consumed family. This is a fact of the ROW GRAMMAR: §2.3's families (i)–(iii) are
> one-step, and the ONLY multi-step row constructions in the displayed grammar are
> the (O3) resummations, all of stopping-word form. [Concrete packs' combined/
> adjusted rows remain clause-4 content — the existing scope sentence stands
> unchanged.]

**WHERE prefix-freeness is discharged for the consumed row-walks: at (b-SW), as a
grammar fact — no new hypothesis.** Consumers re-pointed in r4: (a)'s (O3) bullet
("pairwise disjoint (they differ at the first non-(loop-0) step)" → "pairwise
disjoint by (b-PF)+(b-SW)"), the (O3) exit-scaling line, (c)'s complement reread, and
M2's renewal-equation exhaustiveness note (which cites M1(b)/(d)).

**Proof obligations.** (b-PF): the two-sentence argument displayed above (the
composed-state observation is the only content; it is the same measurable-preimage
reading already used in §1). (b-SW): the one-line prefix check displayed above.
Everything else in (b) survives verbatim.

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

**Contingency (NS-ALL), flagged not priced:** if a verification pass finds a
mandatory consumer needing all-lifts separability FROM M3 at boxes not definitionally
ns-free, that statement becomes an explicit open lemma to price. §4's need check
argues no Step-17/18 need does.

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

**Where (RE) is discharged at the CONSUMED instance.** ROOT Step 18b consumes M2 at
"the intended 𝔅_n instantiation" (through (H5)). The intended instantiation's
booking profile is on file in VERIFIED text: O-12 §1 ("the sealed degree-3 tables =
(O3); the general-n engine = (O1)") + D-11 M1′ (the instance pin). So (RE) at the
consumed member is a DEFINITIONAL DISPLAY (the choice of intended member), warranted
by the verified O-12 record — not a new hypothesis. The concrete pack's conformance
to that member is (H5), unchanged. ROOT r11 displays this discharge at Step 18b
(§7, edit E3) and adds one sentence to the (H5) row (edit E4).

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
reading. **Billing unchanged: (S1-m) + (DET)** — the loop-letter transport is proved
content, so the widening the verifier contemplated is not needed; the honest-widening
paragraph ((S1-m+) under a stochastic hand-off reading) survives verbatim.

### 3.5 FALLBACK [M] member (only if the plan-review rejects §3.3's grammar/pin discharge)

If the reviewer rules that (RE)-at-the-consumed-member cannot ride as a definitional
display (e.g. judging the general-n intended member under-defined until the O-14d
population), the priced form is the following (H5) clause, stated per the PACK-i/ii/iii
genre AT the 𝔅_n member:

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

