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
run at machine clock 2026-08-01 — the ledger's Unit-C convention: the machine
clock trails the directive window — all statements elaborate; `sorry`-only
warnings) but lands only
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
built, all compile-probed GREEN at machine clock 2026-08-01 (`lake env lean`
against head):

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
inputs for the fan-out — both machine-evidenced, machine clock 2026-08-01):**

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
  SCOPE OF THE FINDING, stated exactly (Codex pass-1 finding 10, ACCEPTED):
  the countermodels refute derivability from {e,f ≥ 1, gcd(h_i,e_i) = 1}
  PLUS the coded `Vrec`/`wphi` weight recursion — i.e. from the EXPECTED
  post-ADM-U0 axiom set. If ADM-U0's adjudication lands a DIFFERENT axiom
  set (e.g. a corrected triangularity/normalization constraint from the
  pinned (P3) sheet), the scan must be RE-RUN under it before any "not a
  carrier theorem" conclusion is reused (duty added to ADM-U5); and whether
  the failing probe types are OM-REALIZED is not claimed — the finding's
  force is "these axioms alone do not suffice", matching O-9's own
  attribution ("at general order it follows from (GR-B)"), not a new
  refutation of O-9.

**(c) The open mathematics (door 1) — (ADM-REAL), the general argument over
shape families.** The hypothesis is consumed at REALIZED census data (the
strata Step 14 actually counts). Two tracks; gate G-ADM-2 ROUTES between
them (Codex pass-1 finding 7, ACCEPTED: a finite scan can REFUTE track A
and fire track B, but a no-hit only SUPPORTS track A — the proof burden
stays with ADM-U7's hostile-passed argument; "adjudicates" was an
overstatement and is retired).

* **Track A (primary): prove (ADM-REAL).** Open lemma, with the outer
  quantifiers DISPLAYED (Codex pass-1 finding 8, ACCEPTED): *for every
  degree n ≥ 2, every prime p (wild included), every monic separable
  ns-free f of degree n over ℤ_p, every level N, and every census datum D
  read off a realized OM stratum of the engine's run on f within its (DET)
  window (β_k ≤ eN − 1, heights on the read side's line): every on-line
  slot height satisfies β_k ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)}.* The
  base-changed (O_δ, δ > 1) instances are NOT quantified here — they enter
  through (UB-X)(a)'s transport (the (H4b) row) applied to THIS statement,
  the same division of labor as every (H3) member. The Lean-typed form
  additionally waits on the consumed-data carrier (`consumedData`: the
  Step-14 fan-out's map from realized strata to `CensusData`) — until that
  carrier exists the math statement above IS the statement of record, and
  no Lean unit for it is scheduled (no unit downstream of ADM-U7 exists in
  §4). Proof sketch, section by section: (i) realized on-line slots sit ON
  the read side's line, whose heights are anchored at the entrance floor of
  the frame — the (ZC-a) staircase puts every FRESH read height strictly
  above the accumulated floor F(b) of its block; (ii) the ledger's max
  class weight at order r is bounded by the V̂-layer datum
  (V̂ = e_r f_r w(φ_r); LED-top), itself a FLOOR-layer quantity of the same
  frame; (iii) THE OPEN KERNEL: the comparison (i) ≥ (ii) slot-by-slot —
  floor clearance ⟹ class-weight clearance. HONEST STATUS: (iii) is NOT
  proved anywhere on file; K7's countermodel datum (β₁-relative = 1 < max
  class weight 2 at N = 7, (DET)-legal) shows the inequality can FAIL for
  (DET)-legal ABSTRACT data — so track A succeeds only if realization
  forces MORE than (DET), namely the floor anchoring of (i). Whether K7's
  datum is realized by an actual engine stratum at some (f, p) is the
  question G-ADM-2 probes (finitely).
* **Track B (contingency; fires on a G-ADM-2 hit, or may be elected if
  track A stalls):** generalize the census law instead of pricing the
  hypothesis: CEN-W′ with per-slot factor (q^{dim G_β}−1)·q^{(exponent
  bookkeeping with s(β))} at value-attained slots, digit forced 0 at
  value-unattained interior slots, padding 0 at value-unattained vertices.
  The PER-SLOT ingredient is proved (O-9 rev 4/5 §5.1: read injective on
  G_β, image V_β of dim s(β+1)−s(β), fiber-uniform onto V_β ALWAYS; onto
  F_{r+1} ⟺ FULL; K7's truth value q^{14}(q²−1)(q−1) the worked instance).
  Codex pass-1 finding 9, ACCEPTED: the slot law alone does NOT constitute
  CEN-W′ — still needed are the slot-to-slot iteration/independence
  argument (the same conditional-exactness mechanism CEN-W's own proof
  runs, with onto-F_{r+1} replaced by onto-V_β at each digit), the exact
  exponent bookkeeping, the CEN-J analogue, and re-derivation of every
  census consumer. Track B is therefore TWO units: **ADM-U6a** (design
  note: the CEN-W′ statement + worked K7 instance + ripple map) and
  **ADM-U6b** (the execution program: O-9 rev 6 with CEN-W′ proved end to
  end + fresh hostile passes + Step 14/18 K3-b re-derivation + pack-row
  ripple) — (ADM) retires on U6b's completion ONLY, never on the design
  note. Sign-off-gated (statement change to a verified leaf).

**Numerics gates for (ADM).**

* **G-ADM-1 (pre-run at machine clock 2026-08-01, this lead):** the carrier-lattice CLASS-d
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
  NON-VACUITY duties (Codex pass-1 finding 11, ACCEPTED): (v1) for
  β ∈ D.onLineSlots the filtered class is NONEMPTY — witness: β = D.wt 𝐣
  for some 𝐣 (the def of `onLineSlots`), and 𝐣 lies in its own class — so
  `Finset.sup` is a genuine max, never the empty-sup default; prove this
  first as `lemma classFilter_nonempty_of_mem_onLineSlots`; (v2) D.d ≥ 1 is
  a carrier fact (∏ of the `hf` bounds) — prove `lemma d_pos` and use it
  where `hclass` forces class nonemptiness at arbitrary c. Both lemmas land
  in ADM-U1 so U2's proof consumes them.
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
**The reduction, DISPLAYED (the three verbatim artifacts — folded in at the
Codex pass-1 findings 2/3; quotes from `MOVES_2026-07-24.md` at the cited
lines, re-checkable by grep):**

* MOVES §T.5(2) (lines ~7627–7635): "TB-CAP — (irr)/(hen) PROVED (§T.2,
  conditional on the standing perimeter); (ns) REFUTED as uniformly worded,
  replaced by the displayed (ns-lump) [proved] + (ns-null) [PROVED at rev 2
  …] pair … **VP-SOUND is a CITATION obligation with the two DECLARED
  statements (HEN-LIFT)/(OM-SAT) (§T.2, rev 2)** — the PARI-oracle layers as
  standing refuters. **D4R.0-K(c) is therefore NOT completely discharged:
  what remains is exactly {VP-SOUND's cites}.**"
* MOVES §T.2 "VP-SOUND status" (lines ~7251–7274): "the consumed statements
  now DECLARED PRECISELY … Two named statements: (HEN-LIFT) … (OM-SAT) …
  **VP-SOUND is therefore a CITATION obligation with two declared
  statements, not a gap in the mechanism**". The T-ASSEMBLY rev-5 pass
  record (line ~9123): "the (c) remainder list reduced to {VP-SOUND's
  cites}"; acceptance record (line ~9133): "Conditionality (the note's
  displayed perimeter): open (SIB); conditional (JC-multi); VP-SOUND's two
  declared citations; X.3/CL-4; [2r]".
* MOVES SP.3 SP-COMP conditionality display (lines ~6299–6303): "SP-COMP's
  remaining conditionality is exactly the D4R.0-K(c) residual — the verdict
  pin (alphabet V + halting rule τ + the uniform detection cap), owned by
  [3t] via VP — entering at step (4)'s leaf verdicts."

So "{VP-SOUND's cites}" is not an opaque label: the §T.2 status block names
the set's two members explicitly, and the ENTIRE open content of D-12r = the
two declared citation statements of VP-SOUND:

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

**Dependency decomposition (Codex pass-1 finding 5 — why the OTHER
conditions riding the [3t] acceptance record are NOT D-12r residual; each
routed to its own displayed ledger home):**

| condition on the [3t] record | ledger home (NOT D-12r) | display |
|---|---|---|
| (SIB)/(SIB-STEP), (JC-multi) | Step 15 + the (H7) §3.1 row (engine-stratum application) | ROOT §3.4 item 10: "(SIB)/(SIB-STEP)/(JC-multi) → Step 15 … engine-stratum application = (H7)" |
| X.3/CL-4 (density-form exhaustion) | the drainage/exhaustion chain (Steps 13/19); [3t] §T.0 displays TREE-EXP/TREE-N as X.3-FREE | MOVES §T.0 (lines ~7040–7048) |
| [2r] REL.2 (base-changed sibling factors) | (H4b)/(UB-X)(a) — the O_δ re-base audit | ROOT (UB-X) row |
| (τ-ns) leg's "(z-3) exact identification" | Theorem B case content = D4R.0-K(b), DISCHARGED (dual-verified); the residual (OM-SAT) application "to the key's own chain" is already inside the (OM-SAT) cite | MOVES §T.2 (OM-SAT) bullet, quoted above |
| the O-2 dictionary identification (engine branches ↔ GMN types) | the (H1) group rows (GD-1/(KP) beyond order 1) + the O-2 dictionary node — priced there, inherited here, never re-priced | ROOT §4 item 1 rider: "consumed only through the dictionary node O-2" |
| P(O5t r3) (Step 12's owed hostile pass, which CONSUMES the read-offs) | §3.2 pass-debt row | ROOT Step 12 status line |

The ROOT D-12r row prices exactly the (c)-remainder (its own header:
"the D4R.0-K(c) verdict-pin residual"); the table shows every other
condition has its own priced home, so retiring the two cites empties THIS
row without absorbing any sibling row's debt.

**Why this is not a fiat discharge:** the reduction "(c) remainder =
{VP-SOUND's cites}" is a DISPLAYED, dual-accepted artifact quoted verbatim
above (T-ASSEMBLY rev 5, passes 5+6 CLEAN + Fable pass; the SP-COMP
conditionality display cites it); this blueprint only ROUTES the two cites
through the standing literature process and then synchronizes the ROOT row —
the adjudication-of-executed-reduction case the swarm rules allow. What the
blueprint does NOT claim: that TB-CAP(irr) is unconditional. Its proof
consumes §C Theorem C (C.2) — an ACCEPTED theorem (§C rev 14 dual-accepted,
2026-07-27) — so that leg's status is "proved from accepted-corpus inputs",
the same grade as every other [3t] theorem; the phrase "internal to the
verified corpus" below means exactly this and nothing more (a conditionality
on an accepted theorem's stated perimeter is a CITATION into the corpus, not
an open hypothesis; the D-12r ROW never carried §C's perimeter as its
content — its header names the verdict-pin residual only).

### 2.2 Door assignment: LITERATURE-RETARGET (both cites), Lean upgrade optional

**(HEN-LIFT) faithfulness brief (unit D12R-U1).** (HEN-LIFT) as declared at
MOVES §T.2 is a STATEMENT PACKAGE of three parts, and the brief must pin
each — calling it "one cite" (this blueprint's own pre-fold wording,
corrected at Codex pass-1 finding 6) concealed the count:

* **(HL-a) coprime-factor lifting, existence.** Candidate: **Neukirch,
  Algebraic Number Theory (Grundlehren 322), Ch. II §4 Prop 4.6** — a monic
  (primitive) polynomial over a complete valued field whose reduction
  factors into coprime factors lifts the factorization, degrees preserved.
  ROOT §4 item 5 already carries it as "LITERATURE-CANDIDATE: numbers to
  confirm, Mathlib probe owed"; alternate: **Serre, Corps Locaux I §6**
  (ROOT §3.4 T-U table row). Matching point that can hide a mismatch: the
  ℤ_p[x] MONIC form with MONIC lifts needs the standard leading-unit
  normalization corollary — display the normalization step in the brief.
* **(HL-b) uniqueness of the lift pair** (consumed by VP determinism).
  Neukirch's proof mechanism (coprime Bézout iteration) yields it, but the
  printed STATEMENT may assert existence only: the brief must quote the
  printed uniqueness clause if present, and OTHERWISE display the
  uniqueness argument (two monic coprime-reduction factorizations agreeing
  mod p agree mod p^k by induction) as a COMPANION LEMMA carried by the
  brief itself — a displayed derivation, never a silent strengthening of
  the cite.
* **(HL-c) the read-off: g irreducible + unramified + (E, F) = (1, deg ψ).**
  From ḡ = ψ irreducible: g irreducible over ℚ_p (monic, irreducible
  reduction); ℚ_p[x]/(g) unramified of residue degree deg ψ. Candidate:
  Neukirch II §4 Prop 4.8 / II §6 region, or Serre LF I §6 — a SEPARATE
  numbered statement with its own confirm; it does NOT follow from (HL-a)
  alone and the brief must not present it as if it did.
* Translation risks: none of the wild/tame divide (coprimality, not
  tameness, is the hypothesis — characteristic-free); residue field F_p
  exactly (K = ℚ_p pin, matching the GMN rider's scope discipline); the
  O_δ (δ > 1) re-base reads ride (UB-X)(a), NOT this brief.
* Owed confirmations: the exact numbered statements for (HL-a) AND (HL-c)
  against physical/PDF copies (Neukirch + the Serre alternates), plus the
  (HL-b) disposition (printed clause vs displayed companion), recorded in
  `docs/GMN_citations.md`-style form; only then does the ROOT §4 item-5 row
  drop "LITERATURE-CANDIDATE". Until ALL THREE are pinned, (HEN-LIFT)
  counts as UNCONFIRMED and the D-12r retirement (D12R-U4) may not fire.

**Mathlib probe — RAN by this lead (machine clock 2026-08-01), result NEGATIVE.**
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
(a real formalization, standard math).

**Scope correction (Codex pass-1 finding 4, ACCEPTED): `henLift_padic` as
displayed formalizes (HL-a) ONLY.** The full unit is THREE parts, mirroring
the brief: **D12R-U2a** = `henLift_padic` (existence, the probed signature
above); **D12R-U2b** = `henLift_padic_unique` (same hypotheses, two monic
lift pairs with equal reductions are equal — statement to be compile-probed
at E-phase); **D12R-U2c** = the read-off,

```lean
-- E-phase target shape (NOT yet compile-probed; probe before landing):
-- g monic, g.map PadicInt.toZMod = ψ, ψ irreducible ⟹ Irreducible g
-- (+ the unramified/(E,F) clause in whatever Mathlib vocabulary the prover
--    adjudicates: residue-degree-only numerical form acceptable at first
--    landing, full IsUnramified form as the stretch goal)
```

A landed D12R-U2a alone upgrades NOTHING but (HL-a); the claim "(HEN-LIFT)
VERIFIED-LEAN" requires U2a + U2b + U2c ALL landed — until then the
literature pin remains the operative discharge and D-12r's residual display
must keep all unpinned parts. NOT load-bearing for the door — the faithful
pin suffices at the repo's literature-only-conditionality bar.

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
discipline):** once D12R-U1's (HL-a)/(HL-b)/(HL-c) dispositions + D12R-U3's
pagination confirm are ALL on file (D12R-U2 optional), rewrite the ROOT
D-12r §3.1 row from [M] to the §4 literature class, with the THREE displayed
supports quoted in the row: (i) the §T.5(2) remainder display ("what remains
is exactly {VP-SOUND's cites}") + the §T.2 status block naming the two
members; (ii) the per-part literature pins ((HL-a)/(HL-c) numbered
statements + the (HL-b) disposition; GMN Cor 3.8 + Def 3.9 TAMS-confirmed);
(iii) the dependency-decomposition table of §2.1 above (each sibling
condition at its own priced home). The row's TB-CAP(irr) sentence must read:
"TB-CAP(irr) is PROVED at [3t] from the accepted §C rev-14 Theorem C —
citation into the dual-accepted corpus, not an open hypothesis" — the
precise form of the pre-fold word "internal", which by itself discharges
nothing (Codex pass-1 finding 3, ACCEPTED). Every consuming step's
conditionality line then reads the §4 rows. This is a composition-document
change: it rides the next VC pass (currently VC14 in flight — COORDINATE,
do not race it), and the VC verifier — not this blueprint — adjudicates
whether the rewritten row is faithful.

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

**The architectural HYPOTHESIS the walk must test (route (b)'s substance —
reworded at Codex pass-1 finding 12: what follows is the EXPECTED outcome,
asserted nowhere until the walk displays it site by site):** every FINITE-N
counting object on the mandatory path appears to be thr-scoped by its
displayed definition — the assembly's decided_σ(N) is DEFINED by the
tree-shape sum over thr(T̂) ≤ N (plan §4t input (vii), quoted in the walk);
TB-CAP detection fires within verdict windows joined into N\*(𝐇)
(CU-2t/CU-4's level bookkeeping); the squeeze consumes finite-N counts only
through the two-sided envelope. The walk must CONFIRM each of these at its
consuming display with the display quoted — the CU-4 row's own wording
("perimeter: TB-CAP (D-12r) + (E-N) displayed OPEN") records that the
CURRENT leg treats (E-N) as a condition, which is evidence of pricing, not
of scoped-only consumption; route (b) succeeds exactly if the walk shows
the pricing is dischargeable at every site. CIRCULARITY GUARD (Codex
pass-1 finding 13, ACCEPTED as walk duty W-3): the absorption step — "a
decided box whose unique tree has thr > N sits in the undecided-at-N
envelope drainage prices to 0" — silently uses TWO distinct predicates:
SEMANTIC decidedness (the box fibers a decided ns-free tree) vs OPERATIONAL
decided-at-cap-N (detected by level-N cylinder data). W-3 must quote the
envelope/drainage DEFINITIONS and verify that the envelope is defined as
the complement of the DETECTED-at-N class (in which case absorption is
definitional) rather than semantically (in which case there is a REAL gap
to price and route (b) fails at that site). If the walk verifies all
sites, the unrestricted reading is consumed NOWHERE and (E-N) retires by
RESCOPE (a display change: the caveat remains true and OPEN but prices
nothing on the mandatory path).

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
coincidence depth of a decode. HEURISTIC ONLY, all of it (Codex pass-1
finding 15, ACCEPTED — nothing in this paragraph is a result, including at
n = 2): this lead's scratch, recorded for the prover as ORIENTATION —
disc(f_decode) is a nonzero integer (separable case) of size < p^{c·n·N},
so pairwise root-separation depths obey an integer-size bound whose shape
is ~c·n·N — WRONG SHAPE for the claim at c·n > 1. At n = 2 the same
size count SUGGESTS separations ≲ N (disc < p^{2N+O(1)}), but turning that
into redundancy needs (never displayed anywhere): the exact nonvanishing
case split, the conversion from root separation to the read-ceiling
formula L = I + 1, and the ±1 boundary — so even n = 2 is OPEN. At n ≥ 3
the integer-size argument alone provably does NOT close (v_p(disc) up to
~3N is size-compatible); whether the DECODE constraint (all coefficients
< p^N simultaneously) kills the deep-coincidence range is a
lattice-counting question — heuristically favorable (~p^{2N} decodes vs
~p^{3N} congruence demands) but heuristics are not proofs and special
families (e.g. b = 0 corners) evade counting. VERDICT built into this
blueprint: route (a) is genuinely open at EVERY n; it is scheduled ONLY as
a falsifier-guided attempt, never as a scheduled dependency of the
retirement.

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
  or discharge). Difficulty: easy (def + 2–3 route lemmas).
  DECIDEDNESS ENCODING (Codex pass-1 finding 14, adjudicated MIXED):
  the missing `Decided` premise is DERIVABLE, not missing — `VTree.fiberAt`
  clause 2 (Defs ~518) forces every maximal chain to be halted
  (`IrrHalts … ∨ NsHalts …` with the ns disjunct requiring `Tr.nsLeaf H`),
  and `NsFree Tr` (∀ H ∈ chains, ¬ nsLeaf H) kills the ns disjunct — so
  under the def's hypotheses every maximal chain is a (τ-irr) leaf, i.e.
  the fibered tree IS decided ns-free. The prover MUST land this derivation
  as the auxiliary lemma `fiberAt_nsFree_decided` (spec: NsFree Tr →
  fiberAt … → every maximal chain IrrHalts) BEFORE any consumer cites
  `ENRedundancyAt` as the (E-N) carrier; if the derivation fails to
  compile, the def GAINS the explicit decidedness premise instead (a
  statement fix at E-phase, recorded). DEGENERACY FENCE (same finding):
  the def is per-model (fixed p, F, n, N, m, pol, T, χ); the GLOBAL (E-N)
  carrier is the ∀-closure over presented models at the standing perimeter
  (n ≥ 1, m per the model's chart — the degenerate m = 0 / empty-χ corner
  is excluded by the presented-model constructors, note in the docstring);
  consumers must quantify explicitly, never cite the fixed-parameter Prop
  as the global claim (Codex pass-1 finding 16's genre). NOTE: no proof of
  `ENRedundancyAt` is scheduled — it is the TYPED HOME for route (a) if
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
