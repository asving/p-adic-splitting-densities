# OPEN-MATH CAMPAIGN — 2026-08-16 (owner directive)

**Directive (Asvin, verbatim intent):** set a Fable max-reasoning agent on each open piece of
mathematics. Method, mandatory for every unit: (1) FIRST a high-level outline of proof steps;
(2) each step CERTIFIED before proving — numerical evidence (exact-rational scripts in
`verification/`) and/or survived refutation attempts (constructed counterexamples targeting the
step); (3) only certified steps get proof effort. Honest statuses per step:
PROVED / CERTIFIED-OPEN / REFUTED(+repair) / REDUCES-TO(<row>). A unit that returns a refuted
step has SUCCEEDED. Source of the roster: CHAP-I §3's OPEN-MATH surface (36 rows, grouped) +
the chapter-B residues.

Concurrency: ≤3 fable-max units at once (storm history). Orchestrator watchdog rotates the
queue. Unit notes land in `docs/openmath-campaign/OM-<k>_<slug>_2026-08-16.md`; scripts in
`verification/`; Lean (where a unit reaches it) per the standing fleet rules.

| unit | piece | ledger rows | status |
|---|---|---|---|
| OM-1 | the n=3 rate (hrate₃ → `package_three`) | HYP.08/09/11/28/29 | **DONE** — `package_three` UNCONDITIONAL, (K,B,c)=(1,0,3), Lean-core; HYP.08 strengthened-discharged, HYP.09 discharged; NEW sharp peel branch (S5); P(1)/P(2)/P(3) all theorems |
| OM-2 | GENIND.B, the inductive step — OUTLINE+CERTIFY ONLY | T-1 | **DONE** — 30 rows: 12 landed / 10 reduce / 8 NEW in 3 families (N-1/N-2/N-3), ~15-node sketch, 612/612 certified, S-1 bridge-is-inequality fact; conversion unit chartered |
| OM-3 | the count layer (CS-1/2/EXACT/1Q; A0/A1 per degree) | HYP.23/25/26/30/32/33/35/36/88 | **DONE** — dominance split PROVED (was OPEN), κ(T) a theorem, HYP.88 residue proved, (CS-2) real-count teeth, A0 oracle 0/19758; H63w/H94w landed |
| OM-4 | the σ-ladder pair (LB1)/(MP1) | HYP.41/42 | **DONE** — LB1 REDUCES-TO C.33/C.34; MP1 item 5 = cite #4 (recentered_key_emission, GN15+GMN, drafted); FINDING 0: landed E.39/E.40/E.44 shadows VACUOUS — E carrier strengthening owed before chapter I consumes them |
| OM-5 | B-BOX-1 (the level-2 class-size residue leg) | CHAP-B H-2 residue; CHAP-I addendum routes | **RUNNING** (wave 2) |
| OM-6 | window pinning + the EFF.GENHN.29 transcription gap | HYP.24 | queued |
| OM-7 | GENHN-HE(μ=3) + TOW-1 (incl. the no-owner finding) | HYP.81/82 | queued |
| OM-8 | the deep-twist ∀i≥3 conjunct | HYP.57/63 | queued |
| OM-9 | the weld conjuncts (JD0-BOX-2 side; GENHN-BOX-2 awaits WELD-ZERO pass 2) | HYP.74, HYP.148+139 | queued |
| OM-10 | the n≥8 box family | HYP.67–71/78–80/142/143/144-BOX-2 | queued |

Non-members (orchestrator decisions, not open math): B.43 route re-plan; B.62 norm-bridge
interface. Gate-(b) cites: separate track, owner's signature queue.
