# HDISCHARGE_H3 — discharge blueprint for (ROOT-C)(H3): (ADM) + D-12r + (E-N)

Lead: H3 discharge (hypothesis-discharge swarm, Asvin directive 2026-08-05,
ledger 5a624c3). Date: 2026-08-05 window (machine clock 2026-08-01).
Authority chain: `docs/ROOT_ASSEMBLY_2026-08-02.md` REVISION 12 — the (ROOT-C)
block (H3) + the three §3.1 rows ((ADM) at line ~1468, D-12r ~1475, (E-N) ~1476)
— read at head 08b34d7. Leaf sources of record: `O9_phaseB_verifybrief_rev5.md`
(pass 5 CLEAN, 2026-07-31) · `O1thr_phaseB_verifybrief_rev4.md` (P(O-1thr r4)
owed) · `CU_cluster_phaseB.md` §§0/4 · `MOVES_2026-07-24.md` §§T.1/T.2/T.5
(the [3t] tree note, dual-accepted) + SP.3 SP-COMP · `O3adj_adjudication.md`
risk row R2 · `docs/MATH_COMPLETION_TREE_2026-08-01.md` D-12/D-12r node.

## 0. Charge, scope, rules

**The (H3) row set, verbatim scope (ROOT-C):** "(H3) D-12r (the TB-CAP (τ-irr)
perimeter), (E-N), and (ADM) (O-9's census-admissibility hypothesis, FULL
attainment — automatic at order 0 only; at r ≥ 1 a displayed p-free per-datum
decidable check — §3.1)". Consumed by clauses (SQ)/(R)/(UB) per the §1
attribution ((ADM) by (R)/(UB) only, NOT (SQ) — VC4-4).

**Rules binding this blueprint:** hypothesis content stays hypothesis until
PROVED — no fiat discharge; the ONLY adjudication-grade retirements allowed
here are of already-executed/already-displayed reductions, with artifacts
cited line-by-line. Parked items 22–29 and fenced statements untouched. This
is a BLUEPRINT-ONLY unit: **no Scaffold .lean file lands in this unit** —
every Lean statement below was COMPILE-PROBED against the built corpus
(probe files `/tmp/h3_probe1.lean`, `/tmp/h3_probe2.lean`, `lake env lean`,
2026-08-05: all statements elaborate; `sorry`-only warnings) but lands only
via the prover fan-out waves of §4. New modules go under
`lean/LeanUrat/Scaffold/HDischarge/H3/`, namespace `LeanUrat.Scaffold.HD3`
(Lean unit files) — EXCEPT units explicitly marked as edits to an existing
carrier, which ride the definition-change authority process (Codex diff
confirmation; acceptance = proofs run through).

**Door vocabulary** (per the swarm charge): door 1 = PROVE (argument
sketched section-by-section, open points named); door 2 =
LITERATURE-RETARGET (faithfulness brief: exact candidate published statement,
what must match in our language, translation risks); door 3 =
CONSTRUCTION-CONFORMANCE (which corpus/Scaffold carriers, what conformance
theorem).

**Member-by-member door summary.**

| member | door(s) | one-line route |
|---|---|---|
| (ADM) | 3 + 1 (two-track) | carrier + decidable check ALREADY LANDED (BP_IV; reuse); the open math = (ADM-REAL), FULL attainment at every REALIZED consumed datum — track A proves it over the realized shape families, track B (contingency, statement-change-gated) generalizes CEN-W to arbitrary attainment profiles via the PROVED §5.1 image law, retiring (ADM) wholesale |
| D-12r | 2 (+ 3 optional Lean upgrade) | the residual is ALREADY REDUCED on file (MOVES §T.5 rev 5, dual-accepted: D4R.0-K(c) remainder = exactly {VP-SOUND's cites}); discharge = the two faithfulness briefs (HEN-LIFT ← Neukirch II §4 Prop 4.6 = LIT-3; OM-SAT ← GMN Cor 3.8 + Def 3.9, the §4 item-1 rider) + the owed confirmations + the ROOT-row retirement adjudication; Mathlib probe RAN: coprime-FACTOR Hensel absent (root-lifting only) → optional formalization unit |
| (E-N) | 1 (two-route) | primary route (b): consumption-walk rescope — walk CU-4's F4-C leg + the Step-16 (UB-X)(a) transport and show only the thr-SCOPED count + monotone N→∞ capture are consumed (the unrestricted finite-N reading consumed nowhere) → (E-N) retires to a displayed non-consumed caveat; secondary route (a): prove the redundancy itself (decode-arithmetic argument, open kernel, ±1-boundary risk displayed); two-sided numerics falsifier ADJUDICATES |

---

## 1. (ADM) — O-9's census-admissibility at FULL attainment

### 1.1 Statement of record (verbatim consolidation)

Fix an order-r census datum D (type stages (e_i, h_i, f_i), i = 0..r; ledger
index set J, #J = d·e with d = ∏f_i, e = ∏_{i≥1}e_i; slot weights wt(𝐣) via
the pinned (P3) V-recursion; G_β = the weight-β graded piece;
s(β) = #{𝐣 : wt(𝐣) ≤ β}).

    (ADM)  for every on-line lattice slot k:
           dim_{F_q} G_{β_k} = d
           ⟺ s(β_k + 1) − s(β_k) = d
           ⟺ #{𝐣 : wt(𝐣) ≡ β_k (mod e), wt(𝐣) ≤ β_k} = d.

(the three forms tied by LED(iii), proved at O-9 rev 4/5 §2). p-free,
per-datum DECIDABLE (finite lattice check; at r = 1 the displayed inequality
β_k ≥ h₁((h₁^{−1}β_k mod e₁) + (f₁−1)e₁), collapsing to the value form at
f₁ = 1). Automatic at r = 0 ONLY. NOT automatic at r ≥ 1: two countermodels
on file — K6 (class ⊋ value: e₁ = 3, h₁ = 2, f₀ = f₁ = 1; mod-e display
256/26244 vs truth 0) and K7 (value ⊋ FULL: f₀ = 1, e₁ = 1, f₁ = 2, h₁ = 2,
d = 2; display 73728 vs truth 49152 at q = 2, ratio (q+1)/q per partial
slot). Superseded forms quarantined in the ROOT row: r2 CLASS form, r3 VALUE
form — NEVER consume either. Deep-stratum equivalent reading (available
wherever (ADM) is consumed, since every consumer also assumes (GR-B), via
(CLASS-d)): **(ADM) ⟺ every on-line β_k ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)}**.

### 1.2 Consumption map (where discharge must deliver)

Enters Step 14 (CEN-W/CEN-J) → Step 18's K3 census half (K3-b) AND Step 18b
through seam (S1) AND Step 16/clause (UB) (census over any complete DVR, B1).
Carried by (ROOT-C)(H3); consumed by clauses (R)/(UB) only. Unattained-vertex
data have census 0 (padding), so the hypothesis prices ATTAINMENT, not
positivity. Falsifier state standing: K6 + K7 (+ K7 positive control: census
q^14(q²−1)² EXACT at p ∈ {2,3}, the first d ≥ 2 VALUE gate). O-9 leaf state:
pass 4 SOUND (1 gap) → pass 5 CLEAN (2026-07-31) — the leaf's own reduction
("order-r census REDUCED to (GR-B) + (FRESH) under per-datum decidable
(ADM)") is stable; THIS blueprint discharges the (ADM) factor only.

### 1.3 Door assignment: CONSTRUCTION-CONFORMANCE (landed part) + PROVE (open part)

**(a) Landed and reusable (door 3, REUSE — do not duplicate).** BP_IV already
built, all compile-probed GREEN 2026-08-05 (`lake env lean` against head):

* `LeanUrat.Scaffold.CensusData` + derived `wt/Gset/attainDim/s/onLineSlots`
  (`Scaffold/ValueSide/CensusCore.lean`);
* `LeanUrat.Scaffold.ADMFull : CensusData → Prop` (the FULL-attainment
  predicate, ROOT-row verbatim; `CensusCore.lean` unit H1);
* `Decidable (ADMFull D)` instance (unit C3, `ValueSide/Census.lean`) — the
  "displayed p-free per-datum decidable check" IS ALREADY FORMALIZED;
* `admFull_of_r_eq_zero : D.r = 0 → ADMFull D` (r = 0 automaticity, PROVED);
* `r1Bound` (the displayed r = 1 RHS) + `admFull_r1_iff` (Census.lean:981);
* `censusW` + `census_r0_law` + the C4c gate (`C4cGate.gateData`).

**(b) Two carrier-layer FINDINGS from this lead's probes (adjudication
inputs for the fan-out — both machine-evidenced, 2026-08-05):**

* **(F-ADM-1) The `triangular` axiom degenerates ramified deep stages.**
  `CensusData.triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i` TOGETHER WITH
  `h_coprime : gcd(h i, e i) = 1` forces e_i = 1 at every stage i ≥ 1
  (e_i ∣ h_i ∧ coprime ⟹ e_i = 1). Consequence: the as-built carrier CANNOT
  EXPRESS the K6 countermodel datum (e₁ = 3, h₁ = 2: 3 ∤ 2 fails
  `triangular`) nor any ramified stage-≥1 type; `ADMFull` currently
  quantifies over the e_{≥1} = 1 slice only (where K7 DOES live: e₁ = 1
  passes both axioms). Grep audit: `triangular` is consumed NOWHERE in
  ValueSide beyond the structure and `gateData`'s r = 0 discharge — the
  relaxation ripple is minimal. DISPOSITION (unit ADM-U0): adjudicate
  against O-9 rev5 §1's pinned (P3) data sheet, expected repair = DROP
  `triangular` (keep `h_coprime`), Codex diff confirmation per the
  definition-change authority; K6 becomes expressible and the K6 gate
  (ADM-U4) becomes landable.
* **(F-ADM-2) (CLASS-d) is NOT a bare-carrier theorem at r ≥ 2.** Python
  transcription of the carrier's exact wt lattice (`/tmp/h3_classd.py`):
  under coprime-only axioms, per-class ledger counts #{𝐣 : wt(𝐣) ≡ c} = d
  hold on the full r = 1 grid (0 failures) but FAIL at r = 2 (88 failures on
  the probe grid; smallest: (e₁,h₁,e₂,h₂,f) = (2,1,2,1,1s), period 4,
  weights {0,1,5,6} hit classes 1:1:2:0 — mechanism: w(φ₂) = 4f₁+1 ≡ w(φ₁)
  mod 4, the two class digits collide). This CONFIRMS the O-9 display
  "(CLASS-d) at general order follows from (GR-B)" and REFUTES any plan to
  prove it from the lattice axioms alone. Consequence for unit statements:
  every general-order (CLASS-d)-consuming Lean unit takes (CLASS-d) as a
  NAMED HYPOTHESIS field (supplied at consumption sites by (GR-B), the (H1)
  group — cross-lead seam with H1); the unconditional instances are r ≤ 1.
  CAVEAT for the fan-out: the r = 2 failure grid was generated under
  coprime-only axioms, i.e. AFTER the expected ADM-U0 repair; whether the
  probe types are all OM-REALIZED is not claimed — the finding's force is
  "the carrier axioms alone do not suffice", exactly matching O-9's own
  attribution, not a new refutation of O-9.

**(c) The open mathematics (door 1) — (ADM-REAL), the general argument over
shape families.** The hypothesis is consumed at REALIZED census data (the
strata Step 14 actually counts). Two exclusive tracks; gate G-ADM-2
adjudicates.

* **Track A (primary): prove (ADM-REAL).** Open lemma, stated exactly:
  *at the intended instance, every census datum D consumed by Step 14 —
  i.e. every (type, face, N) datum read off a realized OM stratum of the
  engine within its (DET) window (β_k ≤ eN − 1, heights on the read side's
  line) — satisfies the deep-stratum inequality: every on-line slot height
  β_k ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)}.* Proof sketch, section by
  section: (i) realized on-line slots sit ON the read side's line, whose
  heights are anchored at the entrance floor of the frame — the (ZC-a)
  staircase puts every FRESH read height strictly above the accumulated
  floor F(b) of its block; (ii) the ledger's max class weight at order r is
  bounded by the V̂-layer datum (V̂ = e_r f_r w(φ_r); LED-top), which is
  itself a FLOOR-layer quantity of the same frame; (iii) the open kernel is
  the comparison (i) ≥ (ii) slot-by-slot: floor clearance ⟹ class-weight
  clearance. HONEST STATUS: (iii) is NOT proved anywhere on file; K7's
  countermodel datum (β₁-relative = 1 < max class weight 2 at N = 7,
  (DET)-legal) shows the inequality can FAIL for (DET)-legal ABSTRACT data —
  so track A succeeds only if realization forces MORE than (DET), namely the
  floor anchoring of (i). Whether K7's datum is REALIZED by an actual
  stratum of the engine at some (f, p) is precisely gate G-ADM-2's question.
* **Track B (contingency, fires if G-ADM-2 finds a realized partial slot):**
  generalize the census law instead of pricing the hypothesis: CEN-W′ with
  per-slot factor (q^{dim G_β}−1)·q^{(exponent bookkeeping with s(β))} at
  value-attained slots, digit forced 0 at value-unattained interior slots,
  padding 0 at value-unattained vertices — each slot law ALREADY PROVED at
  O-9 rev 4/5 §5.1 (read injective on G_β, image V_β of dim s(β+1)−s(β),
  fiber-uniform onto V_β ALWAYS; onto F_{r+1} ⟺ FULL). K7's truth value
  q^{14}(q²−1)(q−1) is the worked instance. This retires (ADM) wholesale
  BUT is a STATEMENT CHANGE to the census layer (CEN-W/CEN-J restated,
  O-9 rev 6 + fresh hostile pass + Step 14/18 K3-b re-derivation + pack-row
  ripple) — sign-off-gated, priced at §4's unit ADM-U6, NOT dispatched
  until G-ADM-2 reports.

**Numerics gates for (ADM).**

* **G-ADM-1 (pre-run 2026-08-05, this lead):** the carrier-lattice CLASS-d
  scan — r = 1 grid PASS / r = 2 coprime-only grid FAIL (88) —
  `/tmp/h3_classd.py`, to be re-homed at `verification/h3_classd_scan.py`
  (unit ADM-U5).
* **G-ADM-2 (the adjudicating gate, NOT yet run):** realized-strata
  attainment scan: instrument the existing order-2 census harness (O-9 §10
  K1–K4 lineage, `verification/` + PARI oracle) to LOG the attainment
  profile (dim G_{β_k} vs d) of every realized stratum datum at n ≤ 5,
  p ∈ {2, 3, 5}, N ≤ the harness caps. Output: either "all realized slots
  FULL" (track A supported; the K7 shape is abstract-only) or an explicit
  realized partial-slot instance (track A DEAD; track B fires with the
  instance as its worked gate). Deliverable either way is a committed log +
  a one-page disposition.

### 1.4 Lean unit specs — (ADM)

All statements below COMPILE-PROBED against head (sorry-bodied) unless
marked [EDIT-GATED]. Target files under `lean/LeanUrat/Scaffold/HDischarge/H3/`.

* **ADM-U0 [EDIT-GATED; definition-change authority; wave 0].** Adjudicate
  (F-ADM-1): drop `triangular` from `CensusData` (keep `he/hf/h_coprime`),
  OR record the deliberate e_{≥1} = 1 fence with a rename. Ripple: grep-audited
  (structure + `gateData` only); re-prove `gateData` fields; full
  `lake build` + AxChk. Difficulty: easy (mechanical) but GATED on Codex
  diff confirmation + orchestrator sign-off (landed-carrier statement change).
* **ADM-U1 [wave 0; file `AdmCarrier.lean`].** Per-class count + max class
  weight defs (probed verbatim):

  ```lean
  noncomputable def classCount (D : CensusData) (c : ℕ) : ℕ :=
    (Finset.univ.filter (fun j : D.J => D.wt j % D.period = c % D.period)).card

  noncomputable def maxClassWeight (D : CensusData) (β : ℕ) : ℕ :=
    ((Finset.univ.filter
      (fun j : D.J => D.wt j % D.period = β % D.period)) : Finset D.J).sup D.wt
  ```
  Difficulty: trivial (defs + 2–3 simp lemmas).
* **ADM-U2 [wave 1; `AdmCarrier.lean`].** The deep-stratum reading,
  (CLASS-d) as hypothesis (probed verbatim):

  ```lean
  theorem admFull_iff_maxClassWeight (D : CensusData)
      (hclass : ∀ c, classCount D c = D.d) :
      ADMFull D ↔ ∀ β ∈ D.onLineSlots, maxClassWeight D β ≤ β
  ```
  Proof route: LED(iii) monotonicity — attainDim β counts class weights ≤ β;
  under hclass the class has exactly d members, so = d ⟺ all ≤ β.
  Difficulty: medium-easy (Finset counting). NOTE (F-ADM-2): do NOT attempt
  the hypothesis-free form; r = 2 carrier countermodels on file.
* **ADM-U3 [wave 1; `AdmCarrier.lean`].** (CLASS-d) unconditional at r ≤ 1:
  `theorem classCount_eq_d_of_r_le_one (D : CensusData) (hr : D.r ≤ 1) (c : ℕ) :
  classCount D c = D.d` — transcribes O-9 §2 (CLASS-d) r ≤ 1 proof
  (j₁ = j₁* + t·e₁ enumeration). Difficulty: medium. BLOCKED-BY: ADM-U0 if
  the general (e₁, h₁) range is to be non-vacuous (under as-built axioms the
  r = 1 ramified range is empty — the theorem would compile but quantify
  over e₁ = 1 only).
* **ADM-U4 [wave 1; `AdmGates.lean`].** Compiled countermodel + control
  gates: K7 datum (`¬ ADMFull`, via the `Decidable` instance or explicit
  `Finset` computation — the defs are `noncomputable`, so prefer explicit
  card computations over `decide`; the C4c gate precedent), K7-positive
  datum (`ADMFull`), K6 datum (`¬ ADMFull`) [BLOCKED-BY ADM-U0 —
  inexpressible at head]. Difficulty: easy-medium (Fintype card evaluation
  under noncomputable defs is fiddly; budget accordingly).
* **ADM-U5 [wave 0; numerics].** Re-home `/tmp/h3_classd.py` →
  `verification/h3_classd_scan.py` + G-ADM-2 instrumentation spec
  (attainment-profile logging hooks for the census harness). Difficulty:
  easy (script) / medium (harness hook).
* **ADM-U6 [wave 2; CONTINGENT on G-ADM-2 = partial-slot-found; SIGN-OFF
  GATED].** The CEN-W′ generalization design note (math, not Lean): restate
  CEN-W with per-slot (q^{dim}−1) factors off the §5.1 image law; worked
  K7 instance; ripple map (O-9 rev 6, Step 14, K3-b, pack rows). This unit
  DESIGNS; it does not land the change.
* **ADM-U7 [wave 2; the (ADM-REAL) prover unit; CONTINGENT on G-ADM-2 =
  all-full].** Phase-B style attempt note for track A's kernel (iii)
  (floor clearance ⟹ class-weight clearance at realized reads), against
  the (ZC-a)/LED-top displays; hostile pass owed on completion. Difficulty:
  HARD (open math). This is the group's deepest open point and is honestly
  flagged as such — no unit downstream of it is scheduled.

**(ADM) discharge criterion.** (ADM) leaves the [M] class when EITHER
track A lands (ADM-REAL proved + hostile pass + the ROOT row rewritten to
cite it) OR track B lands (CEN-W′ verified end-to-end and (ADM) deleted from
the consumption chain). Until then every Scaffold consumer keys
`RootHyps.h3_adm` (field refinement: `h3_adm := ∀ D ∈ consumedData, ADMFull D`
once the consumed-data carrier exists — a Step-14 fan-out seam, not this
group's to build).

---

## 2. D-12r — TB-CAP's (τ-irr) completeness perimeter (the D4R.0-K(c) verdict-pin residual)

### 2.1 Statement of record, and the on-file reduction (the load-bearing fact)

ROOT §3.1 row: "TB-CAP's (τ-irr) completeness perimeter: the D4R.0-K(c)
verdict-pin residual — [3t] VP owner; perimeter-conditional wherever TB-CAP
is consumed (Steps 2, 3, 11, 12, 19, and Step 16/clause (UB) through the
(UB-X)(a)-transported layers); displayed, not discharged." Completion-tree
form: O-13's Theorem 4 (realized trees spell inside Sk(n)) is conditional on
SP-COMP's D4R.0-K(c) residual.

**The reduction ALREADY ON FILE (dual-accepted; cite, do not re-prove).**
The kernel D4R.0-K has parts (a) (L1 canonical-choice totality) and (b)
(case-list exhaustiveness) DISCHARGED (D4R0K_DERIVATION rev 3, dual-verified
2026-07-27). Part (c) — the verdict pin — is owned by the [3t] tree note
(MOVES §T.1/T.2, ACCEPTED at the Codex bar 2026-07-27, passes 5+6 clean +
fresh-Fable pass), which discharges: (c1) by definition (VP-1 alphabet +
VP-2 halting rule τ, cell-data-only); (c2) exactly-one-verdict (domain
stratification + covering, conditional on the dual-verified Theorem B);
(c3-a) partition (automatic given (c1)+(c2)); (c3-b) = TB-CAP per clause —
(hen) PROVED (cap N_V = 1), (irr) PROVED conditional on the standing §C C.2
perimeter (§C rev 14 dual-accepted — the conditionality is INTERNAL to the
verified corpus), (ns) literal duty REFUTED and AMENDED by the displayed
(ns-lump) [proved] + (ns-null) [proved, verified clean twice] pair.
MOVES §T.5(2)–(3) + the T-ASSEMBLY rev-5 pass record then display, verbatim:
"the (c) remainder list reduced to **{VP-SOUND's cites}**". So the ENTIRE
open content of D-12r = the two declared citation statements of VP-SOUND
(MOVES §T.2 rev 2, "declared precisely"):

* **(HEN-LIFT)** — f ∈ ℤ_p[x] monic, f̄ = ψ·h̄ with ψ irreducible and
  gcd(ψ, h̄) = 1 ⟹ unique monic lift factorization f = g·h, ḡ = ψ, g
  irreducible generating an unramified extension, (E, F) = (1, deg ψ).
  Valid at ALL primes (coprimality, not tameness, is the hypothesis).
  Discharges (τ-hen)'s read-off.
* **(OM-SAT)** — a realized branch η of T_can(f) with accumulated invariants
  E = ∏e_r, F = ∏g_r and E·F = d(cluster) (⟺ μ = 1 at the last read):
  the branch's cluster factor f_η is IRREDUCIBLE over ℚ_p with e(f_η) = E,
  f(f_η) = F. Discharges (τ-irr), and (τ-ns) modulo (z-3)'s exact
  identification. Consumed as a CITE, never derived from §B2-DEF (which
  supplies the accumulation, not the irreducibility read-off).

Standing refuters riding both cites: the PARI-oracle layers (MENU-n3 (iv),
RESUM-n3) — a misassigned verdict is a decided-type mismatch there.

**Why this is not a fiat discharge:** the reduction "(c) remainder =
{VP-SOUND's cites}" is a DISPLAYED, dual-accepted artifact (T-ASSEMBLY rev 5,
passes 5+6 CLEAN + Fable pass; the SP-COMP conditionality display cites it);
this blueprint only ROUTES the two cites through the standing literature
process and then synchronizes the ROOT row — the adjudication-of-executed-
reduction case the swarm rules allow, with the artifacts named above.

### 2.2 Door assignment: LITERATURE-RETARGET (both cites), Lean upgrade optional

**(HEN-LIFT) faithfulness brief (unit D12R-U1).**
* Candidate published statement: **Neukirch, Algebraic Number Theory
  (Grundlehren 322), Ch. II §4 Prop 4.6** — Hensel's lemma for a complete
  (or henselian) valued field: a primitive polynomial whose reduction
  factors into coprime factors lifts the factorization, degrees preserved on
  the designated factor. ROOT §4 item 5 already carries it as
  "LITERATURE-CANDIDATE: numbers to confirm, Mathlib probe owed"; the §3.4
  T-U table (ROOT line ~1563) pins the alternates: **Serre, Corps Locaux I §6**
  numbers to confirm at declaration.
* What must match in our language: (i) coefficient ring ℤ_p (complete
  DVR) — Neukirch states it for complete valued fields; the ℤ_p[x] monic
  form with monic lifts needs the standard monic normalization corollary
  (leading-unit adjustment) — display this normalization step in the brief,
  it is the one place a mismatch can hide; (ii) UNIQUENESS of the lift pair
  (consumed by VP determinism) — Neukirch's proof gives it via the coprime
  Bézout iteration, but the printed STATEMENT may assert existence only:
  the brief must quote the printed uniqueness clause or supply the
  three-line uniqueness argument (two coprime factorizations with equal
  reductions ⟹ equal by induction on precision) as a DISPLAYED companion
  lemma, not a silent strengthening; (iii) the (E, F) = (1, deg ψ)
  read-off: irreducibility of g from ḡ = ψ irreducible + unramifiedness of
  the generated extension — Neukirch II §4 Prop 4.8/§6 region or Serre LF
  I §6; cite separately, this is a SECOND statement riding the same brief.
* Translation risks: none of the wild/tame divide (coprimality hypothesis is
  characteristic-free); the residue field here is F_p exactly (K = ℚ_p pin,
  matching the GMN rider's scope discipline); the O_δ (δ > 1) re-base reads
  ride (UB-X)(a), NOT this brief (same rule as the GMN rider).
* Owed confirmations: the exact numbered statement against a physical/PDF
  copy (both Neukirch and the Serre alternate), recorded in
  `docs/GMN_citations.md`-style form; then the ROOT §4 item-5 row drops
  "LITERATURE-CANDIDATE" for "pinned".

**Mathlib probe — RAN by this lead (2026-08-05), result NEGATIVE.**
`Mathlib.RingTheory.Henselian` (`HenselianLocalRing`, TFAE at line 119) and
`Mathlib.NumberTheory.Padics.Hensel` (`hensels_lemma`) provide ROOT-lifting
only; grep over the pinned mathlib checkout finds NO coprime-FACTOR
factorization lifting. Consequence: the LIT-3 "Mathlib probe owed" debt is
now PAID with answer "absent"; formalizing (HEN-LIFT) is a genuine unit
(D12R-U2), not a cite of Mathlib.

**(HEN-LIFT) Lean unit (D12R-U2, optional upgrade — probed verbatim, compiles
sorry-bodied at head):**

```lean
open Polynomial in
theorem henLift_padic (p : ℕ) [hp : Fact p.Prime] (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (ψ h : Polynomial (ZMod p)) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h)
    (hfact : f.map (PadicInt.toZMod) = ψ * h) :
    ∃ g k : Polynomial ℤ_[p], g.Monic ∧ k.Monic ∧ f = g * k ∧
      g.map PadicInt.toZMod = ψ ∧ k.map PadicInt.toZMod = h
```

File `HDischarge/H3/HenLift.lean`. Route: successive approximation mod p^k
(Bézout coefficients from `IsCoprime`, completeness via `PadicInt` limits);
or instantiate a general `IsAdicComplete` argument. Difficulty: HARD-medium
(a real formalization, standard math). Add the uniqueness companion
`henLift_padic_unique` (same hypotheses + two lift pairs agree). A landed
D12R-U2 upgrades (HEN-LIFT) from literature pin to VERIFIED-LEAN and shrinks
D-12r's residual to (OM-SAT) alone. NOT load-bearing for the door — the
faithful pin suffices at the repo's literature-only-conditionality bar.

**(OM-SAT) faithfulness brief (unit D12R-U3).**
* Candidate published statement: **[GMN] Guàrdia–Montes–Nart, "Newton
  polygons of higher order in algebraic number theory" (Trans. AMS 364
  (2012); arXiv:0807.2620) — Cor 3.8 + Def 3.9** (order-1 instance Cor 1.20).
  This rider ALREADY EXISTS at ROOT §4 item 1: "LIT-4/(OM-SAT) rides this
  entry by id [audit A-2]: a realized OM branch with residual multiplicity 1
  at its last read certifies an irreducible factor with e = e₁⋯e_r,
  f = f₀⋯f_r; audited scope K = ℚ_p exactly, consumed only through the
  dictionary node O-2". So the brief's job is NOT a new pin — it is
  (i) the printed-TAMS pagination confirmation (the §3.3 debt named on the
  row), (ii) the clause-for-clause match display between MOVES §T.2's
  (OM-SAT) wording and Cor 3.8/Def 3.9's "f-complete/optimal type" wording,
  and (iii) the risk register below.
* What must match: saturation μ = 1 (residual multiplicity one) ⟺ GMN's
  type-singleness hypothesis at the last order; E, F as PRODUCTS of the
  branch data ⟺ GMN e(t), f(t) tower products (Thm 2.11's data); "cluster
  factor certified by the chain" ⟺ GMN's attached p-adic factor (Def 3.9 /
  eq. (37) vocabulary — the SAME identification the dictionary node O-2
  already owns; this brief consumes O-2's dictionary, it does not re-derive
  it).
* Translation risks, displayed: (r-1) GMN's Cor 3.8 speaks of TYPES over
  (ℚ_p-pinned) f; our branches are engine objects — the identification is
  the (H1)/(GR-B)-adjacent dictionary at orders ≥ 2, ALREADY PRICED at the
  (H1) rows; the brief must NOT silently duplicate that pricing — it cites
  O-2's dictionary node and inherits its conditionality display. (r-2) The
  δ > 1 unramified-base reads are (UB-X)(a) content (named at the ROOT §4
  row), not this brief's. (r-3) Attribution risk LOW (the GMN entry is
  the project's central pin, guardian-audited for the index theorem
  already); the residual debt is pagination-confirmation only.

### 2.3 Conformance display + retirement route (unit D12R-U4)

Corpus conformance (door 3, REUSE): TB-CAP's Lean layer exists —
`LeanUrat.MovesT.tbcap_irr` / `tbcap_irr_family` / `tbcap_irr_npband`
(`MovesT/C2_capIrr.lean`, cap = `capIrrOf`/`jetTopLevel`, cross-level
constancy via NP-ID) and `C1_capHen.lean` (hen cap), `C7_nsNull.lean`
((ns-null)) — probed GREEN. These formalize the DETECTION-CAP half at the
carrier layer; they consume no verdict-soundness cite, so they stand
independent of (HEN-LIFT)/(OM-SAT).

**Retirement adjudication (D12R-U4, doc unit, ROOT edit — VC-pass
discipline):** once D12R-U1 + D12R-U3's owed confirmations are on file
(and optionally D12R-U2), rewrite the ROOT D-12r §3.1 row from [M] to the
§4 literature class: "D-12r = VP-SOUND's two cites, pinned (Neukirch II 4.6 /
Serre LF I §6; GMN Cor 3.8 + Def 3.9 TAMS-confirmed); TB-CAP(irr)'s
perimeter internal to the dual-accepted corpus (MOVES §T.5 display)". Every
consuming step's conditionality line then reads the §4 rows. This is a
composition-document change: it rides the next VC pass (currently VC14 in
flight — COORDINATE, do not race it).

**D-12r discharge criterion.** The [M] row retires when the two cites are
pinned-confirmed (+ the row rewrite passes a VC round). Lean upgrade
(D12R-U2) is opportunistic. NO other open mathematics remains in this member
— modulo the honesty note that P(O5t r3) (Step 12's owed pass) carries the
(τ-hen)/(τ-irr) READ-OFF's consumption; that pass debt is a §3.2 row, not
(H3) content, and is NOT absorbed by this blueprint.

---

## 3. (E-N) — O-1thr Theorem 3(c)'s exhaustion caveat (threshold redundancy)

### 3.1 Statement of record

O-1thr rev 4 §6, Theorem 3(c) defines the level-N decided-σ count

    D_σ(N) := #{x level-N : fiber(T, x) for some decided ns-free T
               with type(T) = σ and thr(T) ≤ N}
    and proves D_σ(N) = Σ_{T : type(T)=σ, thr(T) ≤ N} mass(T)·p^{nN}.

**(E-N), verbatim (OPEN):** *whether the clause thr(T) ≤ N inside D_σ(N) is
redundant — i.e. whether a level-N box can fiber a decided ns-free tree of
threshold > N — is NOT settled. A box doing so would be counted by the
unrestricted reading of "decided-σ at level N" and missed by the sum. The
plausibility argument — a level-N decode has no digits at or above N to pin —
is not a proof: deep-frame development coefficients are ℤ-combinations of
digits and key coefficients and can carry any valuation.* Here
thr(T) := max(1, max over T's chains H of L(H)) with L the §3 read ceiling
(any majorant works; only "thr majorizes the tree's own ceilings" is used),
and fiber(T, x) is the six-clause predicate (F1)–(F6) (chains = ALL AND ONLY
realized pruned runs on f_x; certified leaves; Hensel payload; no interior
halts; degree checksums).

### 3.2 Consumption map (the ROOT row, walked to its leaves)

* **CU-4's F4-C leg** (CU_cluster §4): Theorem 3 supplies the fiber-side
  reading for the acceptance certificate; "(E-N) ... touches F4-C's
  decision-level scoping through Theorem 3(c) — displayed, inherited, owned
  by O-1thr". O3adj risk row R2 is the same touch. CU-4's grade:
  RE-LABEL-AS-ASSEMBLY, walk routine but UNWALKED; conditional on
  P(O-1thr r4) + P(O-2a r5) + P(CU-1 r2); perimeter: TB-CAP (D-12r) + (E-N).
* **Step 16 / clause (UB)**: the SAME CU-4/Thm 3(c) content transported at
  q ↦ q^δ through (UB-X)(a) (the §1 B1 attribution).
* ROOT (E-N) row, closing sentence: "Beyond that CU-4 touch and its
  clause-(UB) transport, NO other mandatory-path site consumes it."

**The architectural observation the walk must confirm (route (b)'s
substance):** every FINITE-N counting object on the mandatory path is
thr-scoped BY CONSTRUCTION — the assembly's decided_σ(N) is DEFINED by the
tree-shape sum over thr(T̂) ≤ N (plan §4t input (vii)); TB-CAP detection
fires within verdict windows joined into N\*(𝐇) (CU-2t/CU-4's own level
bookkeeping); the squeeze consumes finite-N counts only through the
two-sided envelope, and a decided box whose (unique — Thm 3(c)) tree has
thr > N is not DETECTED at cap N, i.e. sits in the undecided-at-N envelope
that drainage prices to 0 as N → ∞. If the walk verifies this at every
consuming display, the unrestricted reading is consumed NOWHERE and (E-N)
retires by RESCOPE (a display change: the caveat remains true and OPEN but
prices nothing on the mandatory path).

### 3.3 Door assignment: PROVE, two routes + adjudicating falsifier

**Route (b) — primary: the consumption-walk rescope (unit EN-U1, doc).**
Walk, display-by-display: (i) CU-4 F4-S/F4-C's five supply legs (the §4
assembly display) — record for each whether the consumed count/acceptance
object carries thr ≤ N (expected: yes — F4-C's own hypothesis is
N ≥ N\*(𝐇), a thr-majorant by the N\* join clause); (ii) the O3adj R2 risk
row — re-adjudicate against the walked display; (iii) Step 16's (UB-X)(a)
transport of the same content at q^δ; (iv) the squeeze-side: input (vii)'s
displayed thr-scoped sum + the drainage absorption of the thr>N decided
boxes (cite the envelope displays, Step 13/Step 19). Deliverable: a walk
note in the CU_cluster style with a per-site table (site / consumed object /
thr-scoped? / display quoted), ending in one of: RESCOPE-CLEAN ((E-N)
consumed nowhere unrestricted) or a NAMED consuming site (route (a)
becomes mandatory for that site). HONEST RISK: CU-4's walk is ITSELF unwalked
and conditional on three pending passes (P(O-1thr r4), P(O-2a r5),
P(CU-1 r2)); EN-U1 walks the (E-N)-relevant faces only and must not be
cited as CU-4's full walk.

**Route (a) — secondary: prove the redundancy (unit EN-U3, open math).**
Statement to attempt: *if a level-N box x fibers (working level N) a decided
ns-free tree T, then thr(T) ≤ N* — equivalently, the decode of x (the
zero-extended lift; O-1thr §7's decode vocabulary) realizes no site of read
ceiling > N on a decided ns-free run. Sketch, with the open points named:
(i) the decode's coefficients are the truncated integers < p^N (digits ≥ N
literally zero); (ii) a read at ceiling L > N is pinned by a development
coefficient of w-height ≥ L−O(1) at its frame — for the decode this is an
exact arithmetic coincidence between the truncated integer coefficients and
the accumulated keys; (iii) THE OPEN KERNEL: bound the attainable
coincidence depth of a decode — discriminant-arithmetic heuristics (this
lead's scratch, recorded for the prover): disc(f_decode) is a NONZERO
integer of size < p^{c·n·N}, so root-separation depths are ≤ c·n·N — a
bound of the WRONG SHAPE for the claim at c·n > 1; the n = 2 case squeezes
to separation ≤ N − 1/2 (disc < p^{2N+O(1)}, even valuation split off), so
redundancy holds at n = 2 up to the ±1 boundary of the exact ceiling
formula L = I + 1, BUT at n ≥ 3 the integer-size argument alone does NOT
close (v_p(disc) up to ~3N is size-compatible; whether the DECODE constraint
(all coefficients < p^N simultaneously) kills the deep-coincidence range is
a lattice-counting question — heuristically yes, ~p^{2N} decodes against
~p^{3N} congruence demands, but a heuristic is not a proof and SPECIAL
families (e.g. b = 0 corners) evade counting arguments). VERDICT built into
this blueprint: route (a) is plausibly TRUE-with-margin at n = 2 and
genuinely open at n ≥ 3; it is scheduled ONLY as a falsifier-guided attempt,
never as a scheduled dependency of the retirement.

**The adjudicating falsifier (unit EN-U2, numerics — G-EN-1).** Two-sided
search, small (p, n, N) exhaustive: for every level-N box x (p^{nN} boxes;
p ∈ {2,3}, n ∈ {2,3}, N ≤ 4–5 as budget allows), run the classifier on the
decode (PARI factorpadic oracle + the existing quartic_oracle/census
harness lineage), record: decided-ns-free? tree threshold thr(T) (the
ceiling join, computed from the realized sites), and the flag thr(T) > N.
Outputs: (i) a HIT = a compiled (E-N) counterexample — route (a) DEAD as
stated; the hit box becomes the worked instance for checking route (b)'s
absorption displays (does the hit sit in the undecided-at-N envelope as the
architecture predicts? it MUST — verify numerically); (ii) NO HIT +
margin statistics (min over decided boxes of N − thr) — route (a) supported
at the probed range, margins inform the ±1 boundary analysis. Either way
commit the log to `verification/`.

### 3.4 Lean unit spec — (E-N)

* **EN-U4 [wave 1; file `HDischarge/H3/EnCarrier.lean`]** — the redundancy
  carrier at the presented model layer (probed verbatim, compiles at head):

  ```lean
  def ENRedundancyAt (n N m : ℕ) (pol : CanonPolicy p F)
      (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) : Prop :=
    ∀ (Tr : VTree p F) (x : Box p m),
      NsFree Tr → Tr.fiberAt T χ x → Tr.thr n ≤ N
  ```

  (namespace `LeanUrat.MovesT` vocabulary: `VTree.thr` = the Defs §2.5
  threshold join; `VTree.fiberAt`, `NsFree` as built.) Plus the display
  lemma tying it to the seam contract's `Tr.thr n ≤ N'` rows (Defs ~1646,
  1669: the threshold gate is the SEAM's declared contract shape — the
  carrier makes the (E-N) question a first-class Prop the seam can consume
  or discharge). Difficulty: easy (def + 1–2 route lemmas). NOTE: no proof
  of `ENRedundancyAt` is scheduled — it is the TYPED HOME for route (a) if
  G-EN-1 supports it, and the typed FALSIFIER TARGET if G-EN-1 hits
  (compiled counterexample lands as `¬ ENRedundancyAt …` at the instance).

**(E-N) discharge criterion.** EITHER route (b) lands (walk note verified
RESCOPE-CLEAN + the ROOT (E-N) row rewritten "OPEN, consumed nowhere
unrestricted; scoped count + drainage absorption displayed" through a VC
round) — the expected outcome given the row's own closing sentence — OR
route (a) proves redundancy (then (E-N) retires outright as a PROVED
display). A G-EN-1 hit forces route (b)'s absorption verification and
PERMANENTLY fences route (a).

---

## 4. Unit table, waves, gates (the parallelizable fan-out)

| unit | member | kind | file / deliverable | wave | blocked-by | difficulty | gate |
|---|---|---|---|---|---|---|---|
| ADM-U0 | (ADM) | Lean EDIT [gated: def-change authority] | `Scaffold/ValueSide/CensusCore.lean` (`triangular` adjudication) | 0 | sign-off | easy | full build + AxChk |
| ADM-U1 | (ADM) | Lean defs | `HDischarge/H3/AdmCarrier.lean` | 0 | — | trivial | compiles |
| ADM-U5 | (ADM) | numerics | `verification/h3_classd_scan.py` (+ G-ADM-2 hooks) | 0 | — | easy/med | G-ADM-1 re-run |
| D12R-U1 | D-12r | faithfulness brief | §2.2 brief → `lean/notes/openmath/H3_henlift_brief.md` | 0 | — | easy | number-confirm owed |
| D12R-U3 | D-12r | faithfulness brief | §2.2 brief → `lean/notes/openmath/H3_omsat_brief.md` | 0 | — | easy | TAMS pagination |
| EN-U1 | (E-N) | walk note (doc) | `lean/notes/openmath/H3_en_walk.md` | 0 | — | medium | per-site table complete |
| EN-U2 | (E-N) | numerics | `verification/h3_en_falsifier.py` + log | 0 | — | medium | G-EN-1 |
| ADM-U2 | (ADM) | Lean thm | `AdmCarrier.lean` `admFull_iff_maxClassWeight` | 1 | ADM-U1 | med-easy | — |
| ADM-U3 | (ADM) | Lean thm | `AdmCarrier.lean` `classCount_eq_d_of_r_le_one` | 1 | ADM-U0, ADM-U1 | medium | — |
| ADM-U4 | (ADM) | Lean gates | `HDischarge/H3/AdmGates.lean` (K6/K7/K7⁺) | 1 | ADM-U0 (K6 leg), ADM-U1 | easy-med | compiled ¬ADMFull |
| EN-U4 | (E-N) | Lean def | `HDischarge/H3/EnCarrier.lean` | 1 | — | easy | — |
| D12R-U2 | D-12r | Lean thm (optional) | `HDischarge/H3/HenLift.lean` `henLift_padic` (+ uniqueness) | 1 | — | HARD-med | Lean-core AxChk |
| ADM-U7 | (ADM) | phase-B attempt (open math) | track A (ADM-REAL) note | 2 | G-ADM-2 = all-full | HARD | hostile pass owed |
| ADM-U6 | (ADM) | design note [sign-off gated] | track B CEN-W′ design | 2 | G-ADM-2 = hit | HARD | — |
| EN-U3 | (E-N) | phase-B attempt (open math) | route (a) redundancy note | 2 | G-EN-1 = no-hit | HARD | hostile pass owed |
| D12R-U4 | D-12r | ROOT-row adjudication [VC discipline] | D-12r row rewrite | 2 | D12R-U1+U3 confirms | easy | VC pass |
| EN-U5 | (E-N) | ROOT-row adjudication [VC discipline] | (E-N) row rewrite per EN-U1 outcome | 2 | EN-U1 (+EN-U2) | easy | VC pass |

**Wave shape:** wave 0 = seven fully parallel units (no intra-group deps;
ADM-U0 is the one sign-off gate — dispatch its adjudication request
immediately, it blocks only ADM-U3/ADM-U4's K6 leg); wave 1 = five parallel
Lean units; wave 2 = the two open-math attempts (mutually exclusive per
gate outcomes) + the two ROOT-row adjudications. Prover fan-outs run as
division workflows SEQUENTIALLY per the 429-throttle standing rule.

**Cross-lead seams (declared, not owned here):** (CLASS-d) at orders ≥ 2 is
(GR-B)-supplied — H1's group; consumed here only as a named hypothesis
(ADM-U2's `hclass`). The consumed-data carrier for Step 14 (which data the
census actually reads) is Step-14/BP_IV fan-out territory; (ADM)'s field
refinement waits on it. (UB) transports of D-12r/(E-N) are (H4b)/(UB-X)(a)
content — H4's group; this blueprint only names the entry points. Unit C /
(NSF) interactions: none (no shared carrier; the NsFree conjunct repair
touches `bridgeTree`, not `VTree.fiberAt`).

## 5. Codex adversarial review

Review of THIS blueprint per the swarm directive: run, findings folded, and
the disposition table appended as §6 below (archive:
`lean/notes/openmath/H3_bp_review.md`).
