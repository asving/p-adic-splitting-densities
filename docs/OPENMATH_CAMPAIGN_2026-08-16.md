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
| OM-5 | B-BOX-1 (the level-2 class-size residue leg) | CHAP-B H-2 residue; CHAP-I addendum routes | **DONE** — CITE-CANDIDATE (queue #5, COMPOSITE: Montes dichotomy + Serre/norm glue legs — HELD for explicit owner nod, fallback B.62); proved: the region is entirely off the monogenic-maximal locus; signable Prop + wiring landed |
| OM-6 | window pinning + the EFF.GENHN.29 transcription gap | HYP.24 | **DONE** — 4/5 gaps PROVED at general e₁ (17 Lean decls, H89w, build 8923 green), 1 display clause refuted+repaired (F-OM6.1), reader rule CERTIFIED-OPEN per standing decision, O-2 discharged, HYP.24 CARRY-narrowed |
| OM-7 | GENHN-HE(μ=3) + TOW-1 (incl. the no-owner finding) | HYP.81/82 | **DONE** — O-1 DISCHARGED: μ=3 transcription owner = H73w (H-adjacent, A-H.4; transport + 5-type dictionary + exhaustiveness + μ=2 consistency + HE3.B arithmetic, Lean-core); battery 97/97 GREEN closing all 4 recorded coverage gaps (first embedded n=7, first equal-char μ=3, first D′=4 f₁=2, first h=3); C.93(i) `tower_first_live` PROVED at the signed signature (sharp, fleet-wired); HYP.81/82 both stay CARRY with residues exactly {HYP.143} and {the n≥8 box family} (OM-10); cite-candidate considered and declined (NS-3/NS-9 recorded as option) |
| OM-8 | the deep-twist ∀i≥3 conjunct | HYP.57/63 | **DONE** — HYP.57's named adjudication PERFORMED (S2.1 ⟹ the law at every DEF GENTOW5-1 instantiation w/ canonical read; ρ-defeat REAL at real exponents, so socket typing must pin the canonical read); lattice core Lean-GENERAL (`triangular_descent`/`dvd_stage`) + depths 2/3 concrete + i∈{1,2} transcribed + NODE D.62 landed in leanfinal (A-D.2 signature); HYP.63's empty-base closure PERFORMED (interleaved induction, `wle_of_interleaved` PROVED + footprint walk; residual = suppliers' grades + 1 hostile pass on the C-3/C-5 index reading); numerics 52/0 GREEN both chars (first f₄=3 slots, first non-prime-field deep ϑ, first equal-char rows; naive twin SPLITS at 3 slots); both rows stay CARRY, residuals pinned supply-side |
| OM-9 | the weld conjuncts (JD0-BOX-2 side; GENHN-BOX-2 awaits WELD-ZERO pass 2) | HYP.74, HYP.148+139 | **DONE** — chapter F's FIRST landings: §4+§5 complete in leanfinal (16 files; Display-A carriers `JD0Box2`/`GenhnBox2` + `W1Transport` at gate signatures; 9/15 axiom stubs PROVED incl. F.09 assoc + F.10b power basis; F04w strike⟹perimeter + gauged-cocycle preservation; F12w `w1Transport_iff_zero_iff` — the carrier is the transport's SIGNATURE, machine-checked; fresh `CarryCocycle.c_comm`); 95/0 battery, 8/8 mutants; all 29 theorems Lean-core; HYP.74/148 CARRY + HYP.139 MATH unchanged, residuals pinned; WELD-ZERO fence verified untouched (A-W.2) |
| OM-10 | the n≥8 box family | HYP.67–71/78–80/142/143/144-BOX-2 | **RUNNING** (wave 5, launched 2026-08-16 post-OM-8/9; the roster's last unit) |

Non-members (orchestrator decisions, not open math): B.43 route re-plan; B.62 norm-bridge
interface. Gate-(b) cites: separate track, owner's signature queue.
