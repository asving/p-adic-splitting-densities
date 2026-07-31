# VC3 — end-to-end composition verification of `docs/ROOT_ASSEMBLY_2026-08-02.md` (pass 3)

**Verifier:** Claude (Fable), fresh context — the model-diverse second end-to-end pass
(VC1/VC2 were Codex). Read: the ROOT assembly document ONLY; no prior end-to-end
reports, no leaf records. Charge: composition soundness — the (ROOT-C)/(ROOT) displays
and the quantifier-for-quantifier walk; acyclicity incl. the 17 ≺ 18 ≺ 18b
stratification; the completeness invariant ((ROOT-C) hypotheses vs the §3.1 [M] rows;
consumed inputs vs ledger classes); the three §8 pre-charged spots; every
leaf-consumption against its DECLARED status. Leaf-internal soundness NOT in scope;
declared statements and statuses taken as given. Fix nothing. Line numbers below
reference the document as read (1091 lines).

## VERDICT: COMPOSITION-GAPS

4 blockers (B1–B4), 4 advisories (A5–A8). The §2 walk is acyclic on its declared
Consumes-edges (the 17 ≺ 18 ≺ 18b stratification holds); the (ROOT-C) ↔ §3.1
hypothesis bijection holds (seven [M] rows ↔ H1/H2/H3/H4a/H4b exactly); the three §8
pre-charged spots pass at composition level. But: the "exact" per-clause hypothesis
attribution understates clause (UB) (B1); two consumed PROVED-UNVERIFIED inputs have
no ledger row (O-8b/M14 — B2; B-3 doc level — B4); and Σ_τ R_τ = 1 is credited to the
VERIFIED Step 1 beyond that leaf's declared statement (B3). All four blockers are
display/ledger-integrity repairs of the REVISION-1/2 kind — this pass found no missing
mathematics beyond the displayed (H1)–(H4b).

---

## 1. Findings

### B1 (BLOCKER — hypothesis attribution): clause (UB)'s "exact" attribution omits (H1)–(H3)

Sites: §1 line 110 ("clause (UB) consumes (H4a) + (H4b)"); Step 16 lines 604–605
("exactly as §1 displays"); Step 19 lines 725–726 ("at its displayed conditional scope
((H4a) + (H4b))").

The attribution display bills itself "exact" (line 107), and for clause (R) marks
incremental consumption explicitly ("ADDITIONALLY consumes (H4a)"); the (UB) entry has
no such marker and repeats (H4a), so it reads as (UB)'s FULL hypothesis set. But by the
document's own rows, clause (UB) also consumes (H1)–(H3): the §3.1 (GR-B) row (line
765) lists "Enters Steps 10, 14, **16**, 18, 18b"; Step 16's Consumes-list (lines
608–612) includes Step 8 ((GR-B)-conditional at orders ≥ 2) and Step 14 (the census —
(FRESH)- and (ADM)-conditional at orders ≥ 2); and (UB-X)(a)'s per-leaf O_δ re-base
transports the dictionary/CU/drainage layers whose conditionality includes D-12r and
(E-N). None of these hypotheses evaporates over O_δ; (UB) cannot follow from
(H4a)+(H4b) alone. Consequences: (i) the per-clause reading of (ROOT-C) claims (UB)
provable from (H4a)+(H4b) alone — false; (ii) the §3.1 (ADM) row's Enters-list (line
768: "Step 14 … hence Step 18's K3") correspondingly omits Step 16/(UB). The JOINT
theorem statement (all five hypotheses assumed) is unaffected. This answers the §8
pre-charge question "does any OTHER §3.1 row leak across clauses the same way?" —
yes: (H1)/(H2)/(H3) leak INTO clause (UB), unrecorded (the V2-2 genre, reverse
direction: consumed but unattributed).

### B2 (BLOCKER — completeness invariant): O-8b/M14's PROVED-UNVERIFIED proof is consumed with no ledger row naming its pass

Sites: Step 16 status lines 592–593 ("O-8b **PROVED-UNVERIFIED conditional on
(R1)–(R4)**"); Step 16 Consumes line 611 ("M14's conditional proof (the O-8b attempt
on file)"); Step 18 line 656 ("K3 = [1v]-FULL value correctness ASSEMBLED from T-7s +
O-9's census + O-8b (arbitrary-DVR)"); §3.2 — no row.

§0's vocabulary (line 45): PROVED-UNVERIFIED = "proof on file, pending pass named."
M14/O-8b's pending pass is named nowhere: §3.2 carries a row for every other
PROVED-UNVERIFIED mandatory-path leaf (O-2a, O-1thr, O5t, O-10, O4T, O-9, D-11, O-11,
CUC, CU-1, Dfloor's gaps, the B-layer, K-12) but none for O-8b. Since Step 18's K3-c
places O-8b on the mandatory path of clause (R) — not just (UB) — this is a consumed
input whose [V] debt is in NO ledger class: the exact V2-4/V2-5 failure class. (The
§3.1 (R1)–(R4) row prices the HYPOTHESIS; §6's "(UB-X)/(R1)–(R4) write-up" prices the
[M] write-ups; neither names M14's verification pass.)

### B3 (BLOCKER — attribution/forward reference): Σ_τ R_τ = 1 credited to Step 1 beyond Dfloor's declared statement

Sites: Step 1 statement lines 174–176 ("Hence Σ_τ α(n,τ;p) = 1 at every p, and a
rational function agreeing with 1 at infinitely many arguments is 1: Σ_τ R_τ = 1 in
ℚ(t)") vs Step 1's own Consumes-line 185 ("NOTHING from any later step") and Delivers
line 186–187 ("the Σ_τ R_τ = 1 half of (R)"); Step 19 line 725 ("with Σ_τ R_τ = 1
from Step 1").

The instantiated identity Σ_τ R_τ = 1 needs (a) R_τ's definition (the solve — Steps
2/3/5) and (b) α(n,τ;p) = R_τ(p) at infinitely many p (Steps 18 + 18b, conditional on
(H1)–(H3)+(H4a)). Neither exists at Step 1; Dfloor's declared statement supplies
Σ_τ α = 1 (plus at most the interpolation principle). As displayed, the VERIFIED
leaf-#3 Statement contains a conclusion the leaf cannot even state (R_τ is undefined
in its perimeter) — a textual forward edge inside Step 1 contradicting its own
Consumes-line — and Step 19 consumes the identity "from Step 1", i.e. beyond the
leaf's declared statement (charge item 5's criterion; also the VC1-finding-1 genre, a
Step-1 forward edge). The composition is repairable at Step-19-time with no new
hypothesis (Σα = 1 [Step 1] + α = R_τ ∀p [Steps 18/18b] + the principle ⇒ the
identity; the conditionality is already priced inside clause (R)) — but as written the
derivation locates a conditional conclusion inside a VERIFIED perimeter.

### B4 (BLOCKER — completeness invariant): B-3's document-level PROVED-UNVERIFIED grade missing from the §3.2 B-layer row

Sites: Step 2 lines 211–212 ("**B-3** (Newton-cell volume) core VERIFIED-LEAN
(`L4.lean` `cellVolume_eq`) + PROVED-UNVERIFIED document"); §3.2 B-layer row line 796
(lists B-1, B-2 (doc level), B-4 (order-r layer), B-5, B-6, B-7; B-3 appears only via
its VERIFIED-LEAN core).

V2-4's repair added B-4 to restore three-class completeness. B-3's doc level has the
same status shape as B-2's (Lean-verified core + PROVED-UNVERIFIED June document), and
B-2's doc round IS listed while B-3's is not — a consumed PROVED-UNVERIFIED input
(Step 2 consumes B-1..B-7) whose verification round is scheduled and priced nowhere.
Same class as V2-4; the fix is one list entry.

### A5 (ADVISORY — undisplayed interface match): K3-c's δ > 1 pools vs O-8b's δ-stable position classes

Sites: Step 18 (K3-c, "the base-changed β-legs at q ↦ q^δ, δ > 1"); §3.1 (R1)–(R4) row
line 767 ("wherever verdict rows consume base-changed β-legs (δ > 1 pools)"); Step 16
honest scope lines 595–605 (the law is proved AT δ-STABLE POSITION CLASSES;
exhaustion of the realized ledger = (UB-X)(b)).

O-8b's declared conclusion holds at δ-stable position classes only. The document maps
K3-c's need to the (R1)–(R4) row alone (declared row D-c), implicitly asserting that
the δ > 1 pools consumed at K3-c are δ-stable — but this match is nowhere displayed.
If any K3-c pool were not δ-stable, (UB-X)(b) would leak into clause (R),
contradicting "NO clause other than (UB) consumes (H4b)" (line 110). One sentence at
Step 18 displaying the match (or a re-scope) closes it.

### A6 (ADVISORY — annotation completeness, the V2-7 genre): consumer-list gaps

(i) §4 item 1's GMN consumer list (lines 854–856: "Steps 7, 8, 12, 13, 14, and 15")
omits Step 11 — CU-2t consumes GMN Cor 1.20/3.8 directly (line 451). (ii) The §3.1
D-12r row ("wherever TB-CAP is consumed (Steps 3, 11, 12)", line 770) omits Step 2
(T-6's TB-CAP conditionality declared at line 203) and Step 19 (the bracket consumes
T-6, line 717). (iii) The §3.1 (FRESH) row's Enters-list ("Step 14 … hence Step 18",
line 766) vs Step 10's Delivers-line "the (FRESH) consumption site" (line 446): if
CU-1's step CONSUMES (FRESH), the row omits Step 10 (and clause (SQ) inherits (H2) —
still priced, since (SQ) is attributed (H1)–(H3)); if Step 10 only HOSTS the future
discharge, say so — the current wording reads as consumption.

### A7 (ADVISORY — named flag with no ledger home): OL-O12-1

Named twice at Step 5 (lines 264, 272) as the contingent escape ("fires only if a
future pack departs from 𝔅_n's organizations"); currently unfired and consumed by
nothing. But the §7 closing standard ("every named pin/flag has exactly one ledger
home", line 1011) gives even non-consumed items homes (LC-COH, (REP-IRR), VAL-DIV is
at least labeled in-step); OL-O12-1 has no §3.3 row.

### A8 (ADVISORY — undisplayed identification): T-U's §U.SQ.6 kernel ledger "IS the set of leaves above"

Step 19 lines 715–717. T-U is consumed as VERIFIED-DUAL conditional on its displayed
§U.SQ.6 ledger, discharged by the claim that this ledger EQUALS the Step 1–18b roster
— asserted, not displayed (no row-by-row correspondence). A fresh reader of this
self-contained document cannot check that no §U.SQ.6 item falls outside the steps.
One display table (or a per-item pointer) closes it.

---

## 2. The charge, point by point

**(1) Displays + quantifier-for-quantifier walk.** (ROOT) is displayed as TARGET (§1
lines 62–93) and (ROOT-C) as the theorem-as-proved with (H1)/(H2)/(H3)/(H4a)/(H4b)
(lines 95–123) — both present, honestly distinguished; Step 19 closes at (ROOT-C),
not (ROOT). Clause walk: **(0)** ← Step 1 (VERIFIED, unconditional) — checks.
**(SQ)** bracket ← Steps 1 + 6 (D-15) + 2 (T-6; TB-CAP → D-12r ∈ H3), drainage ←
Step 13 (n ≤ 3 unconditional; general n via (AGR), a §3.2 [V] assembled from
CU-2/CU-4/Cor 4.19, with upstream (H1)–(H3) via the CU layer) — checks under
(H1)–(H3). **(R)** structure and pole-freeness ← Steps 2–5 (+ 17's margins;
(SL≥2) covers the e-quantification), coefficients p-free ← Step 14 (order ≥ 2 under
(H1)/(H2)/(ADM)), value ← Steps 15/16/17/18/18b under (H1)–(H3)+(H4a); Σ_τ R_τ = 1
composable at Step 19 but mis-attributed (B3) — checks under (H1)–(H3)+(H4a).
**(UB)** ← Step 16's displayed scope + (H4b), but ALSO (H1)–(H3) (B1). Under all five
hypotheses jointly, the composition proves (ROOT-C) quantifier-for-quantifier from
the leaves' declared statements + ledger rows; every defect found is
attribution/ledger integrity, not mathematics missing beyond the displayed
hypotheses.

**(2) Acyclicity.** Every §2 Consumes-list references only earlier steps, literature,
or ledgered inputs; the edge-by-edge walk over all 20 steps found no cycle. The
stratification holds as displayed: Step 17 (D-11 M1/M1′/M3) consumes Steps 2/5/6/12
and declares "NOTHING from Steps 18/18b"; Step 18 (O-11) consumes the pack side
(= Step 17, "never M2") and declares "NOT consumed: D-11 M2"; Step 18b (D-11 M2)
consumes Steps 14/17/18 — (S1) ← Step 14, (S2) ← Step 18, (r1) ← Step 17, all
structurally earlier. No CU-7/O5triple cycle: Step 11 discharges Step 12's interface
without consuming Step 12, and Step 10's terminal-ADEQ half is ROUTED to Step 12 (an
ownership split), not consumed forward. Forward MENTIONS of later consumers ((B-INST)
naming Steps 17/18; Deliver lines) are not edges. Sole caveat: the textual forward
reference inside Step 1's statement (B3).

**(3) Completeness invariant.** (ROOT-C) hypotheses ↔ §3.1 [M] rows: EXACTLY EQUAL —
H1 = (GR-B) ≥ 2, H2 = (FRESH), H3 = {D-12r, (E-N), (ADM)}, H4a = (R1)–(R4),
H4b = (UB-X); seven rows, no eighth, no hypothesis without a row, none doubly homed
(§8's re-run paragraph, lines 1070–1075, is accurate). Consumed-input sweep across
all steps: literature lands in §4 (items 1–8, incl. O4T's eight Facts with SEP/DES
in-line-proved, the LIT-8a–e split, Serre CA); pins/flags land in §3.3 (C.1.5/S-1,
D-5, (O6), GD-4/6/7/8, (KP)/(KPirr), (P-ROOT)/(P-KEY)/(FR≡), sloped/sheared,
(I-τ)+K-LOC, (S1)/(S2)/(S3), OL-O12-2, BASE-1(f), LC-COH, (REP-IRR), W3, LIT pins);
[V] debts land in §3.2 — EXCEPT O-8b/M14 (B2) and B-3-doc (B4). OL-O12-1 has no home
(A7; non-consumed). Governance records (the D2.1 re-key, D2.3 recut) are declared
non-inputs; the CUC §0 registry is metadata — consistent.

**(4) The three §8 pre-charged spots.**
- **(SL≥2)** (Step 5 lines 278–303): internally sound. (a) strict inter-block descent
  (L4(i)/(ii): m, μ < e) confines any cycle to one block; (b) block 1 excluded twice
  over (K_1 = (0), Φ_1 = 1, E(1) = {1}; multiplicity-1 hand-off atoms terminate and
  never re-open block-1 states); (c) hence e ≥ 2 at every self-loop, E = e(e+1)/2 ≥ 3,
  exponents E−1 ≥ 2 and E ≥ 3, both denominator forms 1 − q^{1−E}, 1 − q^{−E} units
  of ℛ. Arithmetic checks (e = 2 ⇒ exponent 2), and matches §1's quantified display
  ("e(e+1)/2 − 1 ≥ 2"). Every cited ingredient is a declared O-12 clause within the
  VERIFIED leaf-#2 structural scope. Consumer audit: Steps 5/17/18 consume only
  through e ≥ 2-scoped theorems; no consumer instantiates e = 1; Step 19 consumes via
  Step 5's display (naming Step 19 in the audit sentence would be cosmetic
  completeness). PASSES.
- **(H4a)/(H4b) at Steps 16/18/19:** mutually consistent across §1/16/18/19 for what
  they SAY — (H4a) correctly marked non-(UB)-only (K3-c; D-c threaded at Step 18 and
  §3.1), (H4b) correctly (UB)-only as far as displayed. The failures found are B1
  (the (UB) side understates (H1)–(H3)) and A5 (the δ-stable match undisplayed).
- **(S3) monic/projective split** (Step 18b + §3.3 row): coherent within the
  document — clause (0)'s μ is the monic ensemble (§1 lines 57–58); M2 is consumed at
  monic scope only; the projective reading is annex A-1 per the standing directive
  (§1 "Relation to the tree's root"); (S3) appears in no (ROOT-C) hypothesis; both
  touch points (Step 18b, §3.3) are aligned; Step 5's (g2) covers the weight as a
  rational function only. Verbatim-faithfulness TO D-11 r2 §3 cannot be certified
  from this document alone (the leaf is outside this pass's read scope); within the
  document, the split is consistent and the quoted r2 scoping supports it. PASSES at
  composition level, with that scope note.

**(5) Leaf consumptions vs declared statuses.** Checked per step: T-1/T-8/T-7
re-scopings respected (T-7's [1v]-FULL is assembled at Step 18, never consumed from
T-7; T-8 consumed as formal solve + (REG-p)-conditional, discharged by Steps 4/5);
O-12's honest scope respected (structure/pole-freeness; the mass lemma base is
declared part of the leaf and its VERIFIED grade is the ledger's own wording; value
correctness taken only from 18/18b); O-13's D-12r rider priced (H3); GD23's (GR-B)
rider priced (H1) at Steps 10/14/16/18/18b; O-9 rev-2's (GR-B)/(FRESH)/(ADM)
conditionality priced; O-10's K-LOC/(I-τ) interfaces ledgered [T] and displayed at
Step 18 (D-b); O-14a′ consumed at its twice-stable core + Lean instance;
CU-1/CUC/O5t/O-1thr/O-2a/O4T/D-11/O-11 pass debts all ledgered [V]. Violations found:
Step 19's "Σ_τ R_τ = 1 from Step 1" (B3); O-8b's unledgered pass (B2); B-3-doc (B4).

---

## 3. Non-findings (checked, pass)

- Headline "FOUR of the leaves VERIFIED" consistent with step statuses
  (O-13/O-12/Dfloor/GD23; CU-1 correctly not counted; K-13/T-layer are
  VERIFIED-LEAN/DUAL classes, separately labeled).
- (E-N) is genuinely a hypothesis (touches CU-4 = mandatory path); its H3 slot is
  correct.
- (AGR)'s §3.2 relocation is internally consistent under the ledger's own class
  definitions.
- The eviction list and "explicitly NOT consumed" literature (BNS, DCD, the
  companion): no step consumes them; annex items (htameFE/palindromy, projective
  bridge, (S3)) enter no (ROOT-C) hypothesis.
- §5 numerics are consumed as flags only; no step's proof cites a falsifier as a
  supplier.
- ℛ's definition is sound (units at every real q ≥ 2). Cosmetic only: ℛ ⊂ ℚ(q) at
  line 59 vs "ℛ ⊂ ℚ(t)" at line 65 and "in ℚ(t)" at line 90 — the q = t
  identification is implicit (not counted as a finding).

## 4. Close

**COMPOSITION-GAPS.** Repair sketch (for the next revision, not executed here): B1 =
restate (UB)'s attribution (add (H1)–(H3), or mark the list incremental and drop the
(H4a) repetition); B2 = one §3.2 row naming O-8b/M14's pending pass (or a displayed
re-scope of K3-c); B3 = re-attribute Σ_τ R_τ = 1 (Step 1 supplies Σ_τ α = 1 + the
interpolation principle; Steps 18/18b the tie; conclude at Step 19); B4 = add "B-3
(doc level)" to the §3.2 B-layer row. With those repaired and A5's one-sentence match
displayed, this pass found no remaining composition obstruction on the §2 walk. The
≥ 2 consecutive-clean end-to-end counter remains at ZERO (this pass is not clean).

— VC3 complete (fresh Fable, end-to-end pass 3), 2026-08-02 campaign clock.
