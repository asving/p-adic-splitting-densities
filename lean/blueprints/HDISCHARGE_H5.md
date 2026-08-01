# HDISCHARGE_H5 — the (H5) = (PACK) discharge blueprint (2026-08-05 swarm; H5 lead)

**PROVENANCE.** Directive: the hypothesis-discharge swarm (Asvin 2026-08-05, ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"ASVIN DIRECTIVE (2026-08-05)").
Authority for the row: `docs/ROOT_ASSEMBLY_2026-08-02.md` at REVISION 12 — the
(ROOT-C)(H5) display (§1, lines ~283–302) and the §3.1 **(PACK)** row. Mathematical
core: `lean/notes/openmath/D11_rev4_2026-08-04.md` (the r4 leaf, REVISION 3 text —
its §2A (ROW-Σ) per-booking algebra and §3 (RE) display) +
`lean/notes/openmath/R11_REPAIR_DESIGN_V5_2026-08-04.md` §3.3/§3.5 (the (PACK-iv)
retirement routes (route-a)/(route-b)). Corpus baseline: commit `b314edc`
(all unit statements below COMPILE-PROBED at this HEAD — see §4.0).
**This is a BLUEPRINT-ONLY unit: no Scaffold `.lean` file lands with it; prover
fan-outs run separately.**

---

## 0. The row, restated (what (H5) says — five obligations, one ledger row)

(H5) = (PACK) carries the actual-pack correspondence PLUS four row-laws, all stated
AT THE 𝔅_n ROWS (ROOT §3.1, verbatim content compressed):

* **(clause 4)** the CONCRETE assembled pack (the realized tables whose mass laws
  Step 17's M1 covers; root/entrance rows excluded in-statement by M2's (R-read))
  equals the intended 𝔅_n instantiation ENTRY-FOR-ENTRY (= OL-O12-2's remaining
  DATA half).
* **(PACK-i) rsh_interp** — for every row σ and prime power q₀: the evaluation at
  q₀ of the symbolic shape series Rsh equals Rval(σ)(q₀) (Step 18 K2's Rsh → Rval
  conversion).
* **(PACK-ii) r_bdd** — Rval(σ)(q₀) ∈ [0,1] at every prime power q₀ (what makes
  `ENNReal.ofReal` faithful at K2).
* **(PACK-iii) wsh_ok** — every row's weight/shape series lies in the regular
  subring on which the evaluation ring-hom `evalAt` is defined (K3's membership
  input, with D-6).
* **(PACK-iv) sem_alloc** — the intended member's booking is re-entrant
  ((O1)/(O2′)/(O3), never (O2)), carries NO allocation datum, and its family-(iv)
  verdict rows are the canonical 0/1-coefficient assembly
  row_σ(F) = m(F)·Σ_{comp_F(σ⃗)=σ} ∏_i β_{μ_i}(σ_i)(q^{D_i}), aggregated
  t_σ = Σ_F row_σ(F), with the ONLY adjustments the (O2′) re-feed leg κ₁·x and the
  (O3) exit-row scaling q^E/(q^E−1) — D-11 r4 Theorem M2's premise **(RE)**, a pure
  conjunction (owed-pass C6: (S1)/(S2) do NOT imply it; arbitrary-α members break
  r_bdd, so no clause is derivable from the others).

Consumption (REVISION-12-exact): PACK-i/ii at Step 18's K2 evaluation glue;
PACK-iii at Step 18's K3 ring-hom (with D-6); PACK-iv at its CLOSED two-edge set —
Step 18b DIRECT ((RE) instantiation) + Step 17's E1 (ROW-Σ) delivery display; the
correspondence at Steps 18/18b as the identification the tie evaluates through.

**Standing numerics (flags, never proofs):** the n = 2 real-pack triple
re-derivation (O-11's falsifier) and RESUM-n3 65/65 are the row's executed
instances at n ≤ 3.

---

## 1. Door table (member → door, route, and what would retire it)

Doors: PROVE = argument on file, Lean-provable now at displayed hypotheses ·
LIT = literature-retarget · CONF = construction-conformance (Door 3: build the
object in Lean so the law holds by a conformance theorem; residue displayed).

| member | door | route | Lean deliverable (this blueprint) | retires the ROOT row? |
|---|---|---|---|---|
| clause 4 | **CONF** | route-b constructor; route-a = the n = 3 data pass (design §3.3's ONLY named route-a; n = 2 is falsifier/executed-instance EVIDENCE, not a route — REVISION 2 wording, Codex gap 10) | `packOfMember`/`refOfMember` + self-conformance `PackCorrespondence` (unit C1 — SCAFFOLDING, see the §2.1 caveat); n = 2 instance gate (C4, E-phase-gated); n = 3 = BLOCKED/DATA (C5) | NO — retires only when executed AT THE CONSUMED INSTANCE (OL-O12-2 data pass at n = 3 / O-14d population at general n) |
| (PACK-i) | **PROVE** (block form) + seam note (chain form) | the member's solve β = u⁻¹·t commutes with `evalAt` at every q₀ ≥ 2 (pivot ≠ 0 by margins) | units P0/P1 (PROVED at the 𝔅_n block presentation) | block form YES at the 𝔅_n side; the K2 chain-vocabulary form (`RS4Chain.rsh_interp` at the real instance) rides the chain-instance seam (§2.2) |
| (PACK-ii) | **PROVE at (RE)+MassFacts members** | the symbolic (ROW-Σ) skeleton (Σ_σ β_e = 1) + the nonneg induction ⟹ each value ∈ [0,1] | units R1/R3/B1/B2 | CONDITIONAL YES: proved at members carrying `REWitness`+`MassFacts` (a source-faithful conditionality — the (RE) dependence is REAL, owed-pass C6's arbitrary-α counterexample; C6 motivates the restriction, it does not certify minimality — REVISION 2 wording, Codex gap 6); the INTENDED member's witnesses are open (routes + the M1-shadow follow-on), so no ROOT retirement |
| (PACK-iii) | **PROVE** | `MemRcyc → OKat q₀` bridge + the PROVED Theorem 2 (`BnMember.entries_memRcyc`, landed II-R13) | units K1/K2 | YES for the ENTRIES+LEGS collections (every `T.entries` member and every solved leg, every q₀ ≥ 2 — prime powers included); the identification of "every row's weight/shape series" with those collections + the chain-field seam stay displayed open (REVISION 2 wording, Codex gap 8) |
| (PACK-iv) | **CONF** | typed (RE) carrier + route-b builder; route-a = n = 3 data pass | units D2 (carrier `REWitness`), C2 (`mkREMember`), C5 (route-a spec, BLOCKED/DATA) | NO at the consumed instance until route-a/route-b executes; the CARRIER + builder make the retirement executable |

**The honesty invariant of this blueprint:** nothing here discharges (H5) at ROOT
by fiat. The deliverables split into (a) theorems PROVED at the 𝔅_n side (PACK-iii
fully; PACK-i block form; PACK-ii conditional on (RE)+MassFacts — each a NEW
machine-checked asset shrinking the row's mathematical content), and (b) typed
carriers + constructors making the remaining content a FINITE EXECUTABLE
conformance check (clause 4, PACK-iv). The ROOT §3.1 row text is untouched by this
unit; row edits ride the next ROOT revision after prover fan-outs land.

---

## 2. Member-by-member analysis

### 2.1 Clause 4 (the correspondence) — CONF

**Landed carriers (BP_IV units H2a/H2b, `Scaffold/ValueSide/Hyps.lean`, all green):**
`AssembledPack n` (finite row table: `Row`/`entry : Row → RatFunc ℚ`/`blockOf`),
`PackReference n C P` (the intended reading, keyed to `C : UCarriers n`),
`PackCorrespondence n C P R : Prop` (`entry_eq` + `block_eq`). The BP_IV S5b
consumer (`seriesTie_of_kernels`) already binds `hpack : PackCorrespondence` —
the K2 consumption shape is settled; S5b itself is owner-blocked (its header).

**Seam adjudicated (two carriers, one content — REUSE, no third carrier):** BP_II
charters `InstancePin (p n) (D : RegData p) (T : BnMember n)` ((B-INST), II-G5 —
in the BP_II mop-up queue, NOT landed at `b314edc`; `Scaffold/O12/RegEmpty.lean`
names it in prose only). (B-INST) pins realized `RegData` tables to a `BnMember`;
`PackCorrespondence` pins an `AssembledPack` to a `UCarriers`-keyed reference.
Same mathematical row (clause 4), two consumption vocabularies (Movement II
zeros/poles vs Movement IV value side). RULING for H5 units: build on the LANDED
BP_IV pair; C3's REVISION-2 `ref_reads_member` field is the T↔R ENTRY-LEVEL tie
inside the bundle, and II-G5's `InstancePin`, when BP_II lands it, supplies the
`RegData`-side pin — the equivalence-or-implication theorem between the two pins
is CHARTERED as follow-on unit **F2** (owner: whoever lands second, per the
opaque-parameter precedent), replacing the r1 "plug-slot comment" (Codex gap 12:
a comment is not deduplication). H5 does NOT declare `InstancePin` (owner: BP_II).

**Route-b (general n).** Define the pack READ OFF the member
(`packOfMember T := the Σ-type table over T.entries`) and the reference reading
the SAME member (`refOfMember`); `PackCorrespondence` then holds by `rfl`-class
proof (unit C1). TWO caveats, displayed [REVISION 2, Codex gap 9]: (i) this is
a SELF-conformance — scaffolding for the route, NOT clause-4 law-transfer; the
transfer claim needs the row-identity seam (C3's `ref_reads_member` at the
entry level now; the σ-keyed row pin = F2/route territory); (ii) the Σ-type
over `Finset Qq` COLLAPSES distinct table rows carrying equal rational-function
entries — "entry-for-entry" at the source is a statement about TABLE POSITIONS;
a multiset/position-indexed `Row` refinement is the E-phase option if the
O-14d population needs position fidelity (flagged to C1's prover, decision
recorded at landing). What remains open is the identification of the REALIZED
corpus tables (the classifier-built pack that Steps 17/18 actually consume)
with `packOfMember` of the intended member: that is exactly OL-O12-2's data
half / the O-14d population duty, and it STAYS the row's open content until
executed (route-a at n = 3; O-14d construction at general n). No unit here
claims it.

**Route-a (n ≤ 3 instances).** n = 2: the corpus has the DEVICE chain
(`MovesS/N2Sigmas.lean`) and the real-pack numerics; the M04 F1 fence stands —
"the DEVICE n = 2 chain must never instantiate S5's carriers (its Rval triple is
refuted against the true densities)". So the n = 2 instance unit (C4) is
E-PHASE-GATED: its carrier choice (which n = 2 table plays `AssembledPack 2`, and
which reference is HONEST — the S-area real pack, not the device chain) needs a
one-paragraph adjudication against the F1 fence before any prover runs. n = 3:
no Lean-side tables exist (RESUM-n3 is a Python numerics record, 65/65 exact);
unit C5 is a SPEC ONLY, tagged BLOCKED/DATA.

### 2.2 (PACK-i) rsh_interp — PROVE (block form); the chain form is a named seam

**What the ROOT row needs mathematically:** solve-then-evaluate =
evaluate-then-solve at every prime power q₀, at the member's rows. At the 𝔅_n
block presentation (landed: `BlockPresentation` with
`hsolve : β e σ = u⁻¹ * trow σ`, `hu : u ≠ 0 ∧ MemRcyc u ∧ MemRcyc u⁻¹`), the
block form is: `evalAt q₀ ⟨β e σ, _⟩ = (evalAt q₀ ⟨u, _⟩)⁻¹ * evalAt q₀ ⟨trow σ, _⟩`,
with `evalAt q₀ ⟨u, _⟩ ≠ 0`. Inputs, all landed or unit-K: `evalAt` is a ring hom
on `OKat q₀` (`MovesS/Defs.lean:305`); memberships via K1/K2; the inverse law via
K3 (`evalAt_inv`); nonvanishing of u at q₀ ≥ 2: u = solveU = 1 − q·q^{−E} with
E ≥ 3, so eval = 1 − q₀^{1−E} ≥ 3/4 (unit P0 — the Corollary D margin at the
scalar; cf. `bn_substochastic_margin`, `Scaffold/O12/Substochastic.lean:93`, and
`MemRcyc.eval_ne_zero_of_inv`, `MovesU/O12PoleFree.lean:191`).

**The chain-vocabulary form** (`RS4Chain.rsh_interp` — `Rsh`, the S-side Cramer
matrix solve, evaluated to `Rval`): the corpus consumption site is
`evalℝ_eq_Rval_of_solvePin` (`Scaffold/ValueSide/SeriesTie.lean`, landed), which
consumes the field AT AN INSTANCE. Constructing the real general-n `RS4Chain`
instance (30+ fields, measure side included) is NOT H5 scope — it is the
D-11/O-14d instance-population unit shared with route-b. NAMED SEAM, displayed
here so no consumer mistakes the block-form theorem for the chain field: H5
delivers the row-law AT THE 𝔅_n ROWS (P1); the instance construction consumes P1
for its `rsh_interp` field when it runs. [The n = 2 device chain's field is
proved (`n2_rsh_interp`, `MovesS/N2Sigmas.lean:947`) — evidence of the pattern,
fenced from value claims by F1.]

### 2.3 (PACK-ii) r_bdd — PROVE at (RE)+MassFacts members

**Why conditional:** the owed pass's finding C6 (pass 3, 6 criticals) exhibited
arbitrary-allocation members whose rows leave [0,1] while satisfying (S1)/(S2) —
r_bdd at the intended member RIDES the row-form profile. The honest theorem is
therefore: (RE) + the mass facts ⟹ values in [0,1]. This is not a weakening —
it is exactly the leaf's own dependency structure ((ROW-Σ) consumes (RE); ROOT
prices (RE) at the consumed member as (PACK-iv)).

**The chain, at ℚ(q) level then evaluated (the §3 core):**
1. Σ_σ β_e(σ) = 1 SYMBOLICALLY in ℚ(q) (unit R1, the (ROW-Σ)(a) skeleton).
2. `evalAt q₀` is a ring hom ⟹ Σ_σ evalAt(β_e(σ)) = 1 at every q₀ ≥ 2 (unit R3).
3. evalAt(β_e(σ)) ≥ 0 by strong induction on e (masses nonneg at q₀ (MNN) +
   legs nonneg by IH through `powSubst_evalAt` at the child pool q₀^{D_i} ≥ 2 +
   pivot > 0) (unit B1).
4. 0 ≤ x_σ with Σ x_σ = 1 ⟹ each x_σ ∈ [0,1] (unit B2). ∎

### 2.4 (PACK-iii) wsh_ok — PROVE (the cheapest full member)

Landed: `BnMember.entries_memRcyc` (Theorem 2, II-R13, PROVED — every generated
entry in ℛ_cyc) and `beta_memRcyc` (II-R5, every solved leg). Landed:
`MemRcyc.definedAt` (L7(i) — denominator nonzero at every x ≥ 2). MISSING at
`b314edc` (grep: zero hits for `OKat` in `MovesU/O12PoleFree.lean` or
`Scaffold/O12/`): the one-step bridge `MemRcyc f → 2 ≤ q₀ → f ∈ MovesS.OKat q₀`
(same proof skeleton as `MemRcyc.definedAt`: `MemRcyc.eq_div` presents f = P/s,
`RatFunc.denom_div_dvd` divides the reduced denominator into s, `cycS_eval_pos`
kills the zero). Units K1 (bridge) + K2 (both quantified corollaries at
`BnMember`). SCOPE, exact [REVISION 2, Codex gap 8 — the r1 "in full" claim
narrowed]: this proves regularity for the two corpus collections — every
`T.entries` member AND every solved leg `T.β e σ` — at every q₀ ≥ 2, prime
powers included. The source sentence quantifies over "every row's weight/shape
series"; the identification of ALL such series with (subring-closed
combinations of) these two collections, and the transport into the chain field
`RS4Chain.wsh_ok` at the real instance, are DISPLAYED remaining seams (§2.2's
chain-instance seam; `OKat q₀` is a `Subring`, so sums/products of covered
series stay covered — the residue is the roster identification, not closure).
[D-6 in the ROOT display is the K3 consumption partner (evalAt's ring-hom
laws), already landed as `MovesS.evalAt`; no new obligation.]

### 2.5 (PACK-iv) sem_alloc — CONF (carrier + builder now; data/population later)

**Carrier (unit D2):** `REWitness T` types (RE)'s OPERATIVE content at the
corpus carrier [REVISION 2 wording; the r1 "exactly" claim withdrawn — §4.2
(δ4)] — the member's booking is re-entrant (`T.booking ≠ Booking.O2`); the
member's carried ROWS are the canonical assembly with only the displayed
booking adjustments (`row`/`row_eq_displayed` at `displayedRow`'s three forms,
tied to the entry roster by `row_mem_entries`; the block aggregate pinned by
`trow_canonical` to `tRow` built from `rowOf` — the corpus's own §2.3(iv)
transcription, II-R8); hand-offs descend (L4 clause). "No allocation datum"
compiles to the row-form pair per the (δ4) adjudication (§4.2) — α-freeness
of the rows is a consequence; the literal no-datum clause is an at-instance
residue, displayed. The (O2′)/(O3) adjustments live in `displayedRow`
(unit D1), pinned to the leaf's three displayed forms.
**Faithfulness deltas, displayed (trust surface for the Codex pass):**
(δ1) the corpus `BookingSystem` carries ONE booking for the whole member, so
"EVERY block booked re-entrantly" compiles to the single-field disequality —
faithful at the corpus's own granularity (BP_II transcribed 𝔅_n that way);
(δ2) `BnCoordinates.handoffs/composition` are per-BLOCK aggregates while the
§2.3(iv) display is per-EXIT-STRATUM (H(F), comp_F) — `ExitData` (unit D1) is
the per-stratum refinement the row-form needs; the compatibility proposition
(`ExitData` aggregates to the member's `BnCoordinates.handoffs/composition`)
is CHARTERED as follow-on unit **F1** [REVISION 2, Codex gap 12 — a chartered
proposition, not a bare flag], owner BP_II-side at its next touch; (δ3) the O2
branch of `displayedRow` is a guarded placeholder (= the unadjusted t), NEVER
consumed under `booking_reentrant` — the same junk-value-plus-guard convention
as `Booking.kernel` at e ≤ 1; GUARDED-API DISCIPLINE [REVISION 2, Codex gap
11]: `displayedRow` is public and its TYPE carries no guard, so every H5
theorem about it is keyed by an explicit booking equality or
`booking_reentrant` binder (R2's three theorems are; graders check any future
consumer for the same key — an unguarded generic consumer reading the O2
branch reads fabricated data).

**Builder (unit C2, route-b's Lean face) [REVISION 2 per Codex critical 2]:**
`mkREMember` — from re-entrant-booked coordinates with rows DEFINED
canonically, produce the `BnMember` together with its `REWitness` — INCLUDING
the REVISION-2 row fields: the builder SETS `row e σ := displayedRow …`, so
`row_eq_displayed` is `rfl` and `row_mem_entries` is discharged by putting the
constructed rows INTO the built member's `entries` roster (a builder duty, not
an assumption). What "by construction" then honestly covers: the (RE)
OPERATIVE content per (δ4) at the CONSTRUCTED member — design §3.3 (route-b)'s
"the profile then holds BY CONSTRUCTION and is checkable at population time".
The identification of the consumed member with the constructed one stays
clause-4/route territory (§2.1). Route-a (n = 3) stays a data pass: unit C5's
spec names the per-row duty (verify each sealed block's booking against the
(O3) forms and each row against §2.3(iv) + the displayed scaling) — executable
only when n = 3 tables land in Lean; BLOCKED/DATA.

**(ROW-Σ) delivery tie:** the leaf's (ROW-Σ) is a PROVED theorem consuming (RE);
units R1/R2 are its ALGEBRAIC SKELETON at the symbolic level (§3) — so once a
consumed member carries `REWitness` + `MassFacts`, Step 17's E1 delivery display
has a machine-checked core standing under it.

---

## 3. The mathematical core: the symbolic (ROW-Σ) skeleton (units R1/R2/R3)

**Relation to the leaf, stated exactly (honesty over elegance).** D-11 r4 §2A
proves (ROW-Σ) PER PRIME POWER q₀, with the mass input supplied SEMANTICALLY
(M1(a) families (ii)/(iii): m(F)(q₀) = P(F | C_e); M1(d): one-step strata masses
sum to 1). The Lean skeleton proves the SAME algebra one level up, at ℚ(q), with
the mass input carried as the named hypothesis structure `MassFacts`:

* **(EXM)** Σ_{F ∈ Exits(e)} m(F) = 1 − κ₀ − κ₁ in ℚ(q), per block 2 ≤ e ≤ n —
  the exit-mass completeness identity (the leaf's step 2 output, symbolically);
* **(BASE)** Σ_σ β_e(σ) = 1 at e ≤ 1 (block 1 = the trivial solve, one decided
  verdict with β = 1 — O-12 §2.3's preamble);
* **(MNN)** each mass evaluates ≥ 0 at every q₀ ≥ 2 (counts over F_q — true at
  the intended member by construction; needed only for unit B1, not R1).

Both (EXM) and (BASE) are FINITE PER-MEMBER ALGEBRAIC DATA — at the intended
member they are exactly the M08-census shadow (level-1 census law, M08 Theorem 2;
BP_IV C4c `census_r0_law` territory) and NOT proved here: H5 charters the algebra
that CONSUMES them, and displays them as the M1 shadow. Deriving (EXM) at the
intended member from the census layer is a named FOLLOW-ON (owner: D-11/O-14d
with BP_IV's census units; out of this blueprint's wave plan).
STRENGTH NOTE [REVISION 2, Codex gap 7]: symbolic (EXM) in ℚ(q) is a priori
STRONGER than the leaf's consumed mass input (M1(a)/(d) supply the identity
PER prime-power evaluation). The two are equivalent FOR REGULAR FAMILIES: the
member's masses lie in ℛ_cyc (`mass_memRcyc`), and two rational functions
regular on [2, ∞) that agree at the infinitely many prime powers are EQUAL —
so per-q₀ (EXM) at all prime powers forces symbolic (EXM). This derivation is
itself a chartered follow-on lemma (**F3**, EASY/MED: `RatFunc` equality from
infinite agreement via `Polynomial.eq_of_infinite_eval_eq`-class Mathlib
facts), NOT assumed by R1 — R1 simply takes symbolic (EXM) as the displayed
hypothesis, and the F3 route is how the census layer will discharge it.

**Theorem (R1, symbolic (ROW-Σ)(a)).** T : BnMember n, W : REWitness T,
M : MassFacts T W. Then Σ_σ β_e(σ) = 1 in ℚ(q) for every e ≤ n.

*Proof sketch (mirrors leaf §2A.2, steps renamed to units).*
Strong induction on e (`Nat.strong_induction_on`, the `beta_memRcyc` pattern).
* e ≤ 1: (BASE).
* 2 ≤ e ≤ n: `hsolve` + `hblockU` give β_e(σ) = u⁻¹·t_σ with
  u = solveU(booking, e) = 1 − q·q^{−E} (re-entrant branch, fired by
  `booking_reentrant`; `kappa_add` rewrites 1 − κ₀ − κ₁ = u). Then
  1. **[telescoping, unit K4]** Σ_σ t_σ = Σ_F m(F)·∏_i (Σ_{σ'} powSubst D_i
     (β_{μ_i}(σ'))): `rowOf`'s comp-fibers partition the tuple space (comp_F
     total ⟹ `Finset.sum_fiberwise`-class), and the pi-type sum factors
     (`Finset.prod_univ_sum`). No convergence content — finite index types.
  2. **[leg normalization]** each inner sum = powSubst D_i (Σ_{σ'} β_{μ_i}(σ'))
     = powSubst D_i 1 = 1: `powSubst` is a ring hom (`map_sum`/`map_one`,
     landed `MovesS/PowSubst.lean`), μ_i < e by `handoff_lt`, IH applies
     (μ_i < e ≤ n). NOTE the symbolic level makes the leaf's "uniform in q₀ so
     the IH applies at child pools q₀^{D_i}" bookkeeping DISAPPEAR — the base
     change is the ring hom powSubst, and the IH is one symbolic identity.
  3. **[mass input]** Σ_σ t_σ = Σ_F m(F) = 1 − κ₀ − κ₁ = u by (EXM) + kappa_add.
  4. **[close]** Σ_σ β_e(σ) = u⁻¹·u = 1 (u ≠ 0 = `hu.1`). ∎

**Theorem (R2, symbolic (ROW-Σ)(b)) — the three booking totals.** Same
hypotheses; S_e := Σ_σ displayedRow(booking, e, β, exits e, σ). Then
* (O1):  S_e = 1 − κ₀ − κ₁  (= Φ^{(O1)}; steps 1–3 alone);
* (O2′): S_e = (1 − κ₀ − κ₁) + κ₁·(Σ_σ β_e(σ)) = 1 − κ₀  (consumes R1 at e);
* (O3):  S_e = q^E/(q^E − 1)·(1 − κ₀ − κ₁) = 1 − (q−1)/(q^E − 1)  (`field_simp`/
  `ring` against `qX^E − 1 ≠ 0`, the landed `kernel_ne_zero` ingredient).
Matches leaf §2A.1(b) EXACTLY (three DIFFERENT values; no booking's displayed
total is 1) — the round-4-finding-2 honesty display, machine-checked.

**Theorem (R3, evaluated (ROW-Σ)(a)).** Σ_σ evalAt q₀ ⟨β_e(σ), _⟩ = 1 at every
q₀ ≥ 2 (memberships from K2; `map_sum` of the ring hom + R1). This is the form
unit B2 consumes and the (PACK-ii) upper bound rides.

**Falsifier discipline for R1/R2 (pre-registered):** at n = 2 the identities are
checkable against the machine-checked n = 2 tables (α₂-side: Σ_σ β₂(σ) = 1 with
β the landed N2 solve values) — if the symbolic skeleton fails there, the
carrier transcription (D1/D2), not the leaf, is the first suspect. Numeric
cross-check: `verification/` RESUM-n3 65/65 already exercises the n = 3
instances of exactly these totals (ROOT row's numerics column).

---

## 4. Lean unit specs

### 4.0 Compile-probe record (the BP_VI/BP_IV lesson executed)

TWO probe rounds, both against HEAD `b314edc`, one file each importing
`Scaffold.O12.Family`, `Scaffold.ValueSide.Hyps`, `MovesS.PowSubstOK`:
* **r1 probe**: the original statement set — 8 sorry warnings, ZERO errors
  (two fixes folded during probing: `ValueSide.` qualification on
  `AssembledPack` outside the `open`; `rowsOf : ℕ → Finset Qq` binder typing).
* **r2 probe (post-Codex fold)**: every REVISION-2-changed statement —
  `REWitness` (row-indexed), `MassFacts` (completed), B1 (`e ≤ n` + inner
  pool quantifier), `H5PackTyped` (five-field form), P1 (now probed, clearing
  the r1 PROBE-OWED tag), P0 both halves — 4 sorry warnings, ZERO errors.
Statement shapes are therefore ELABORATION-SAFE at HEAD; provers may adjust
implicit binders/instance arguments per the standing BP_II §1 rule, never
mathematical content. Probe files deleted after recording (blueprint-only
unit); the r2 statements above are the ones IN this document.

### 4.1 Files (all NEW, under `lean/LeanUrat/Scaffold/HDischarge/H5/`)

| file | units | imports |
|---|---|---|
| `Defs.lean` | D1, D2 | `Scaffold.O12.Family` |
| `Kernels.lean` | K1, K2, K3, K4 | `Defs.lean` + `MovesS.PowSubstOK` |
| `RowSigma.lean` | R1, R2, R3 | `Kernels.lean` |
| `Bdd.lean` | B1, B2 | `RowSigma.lean` |
| `PackI.lean` | P0, P1 | `Kernels.lean` |
| `Conform.lean` | C1, C2, C3 (+ C4/C5 specs) | `Defs.lean` + `Scaffold.ValueSide.Hyps` |

Namespace: `LeanUrat.Scaffold.HDischarge.H5`, with
`open LeanUrat.MovesU (MemRcyc SplittingType)` and
`open LeanUrat.MovesS (OKat evalAt powSubst)` as probed.

### 4.2 Wave 0 — carriers (`Defs.lean`; MECH; Codex statement-audit REQUIRED before consumption — new trust surface)

**D1 (carriers `ExitData`/`tRow`/`displayedRow`).** Verbatim (probed):

```lean
structure ExitData (n : ℕ) where
  idx : Type
  instF : Fintype idx
  mass : idx → Qq
  handoff : idx → List (ℕ × ℕ+)
  comp : ∀ F : idx,
    ((i : Fin (handoff F).length) → SplittingType n) → SplittingType n

attribute [instance] ExitData.instF

noncomputable def tRow {n : ℕ} (β : ℕ → SplittingType n → Qq)
    (E : ExitData n) (σ : SplittingType n) : Qq :=
  ∑ F : E.idx, rowOf β (E.mass F) (E.handoff F) (E.comp F) σ

noncomputable def displayedRow {n : ℕ} (b : Booking) (e : ℕ)
    (β : ℕ → SplittingType n → Qq) (E : ExitData n)
    (σ : SplittingType n) : Qq :=
  match b with
  | Booking.O1 => tRow β E σ
  | Booking.O2 => tRow β E σ   -- guarded placeholder; never consumed under (RE)
  | Booking.O2r => tRow β E σ + kappa1 e * β e σ
  | Booking.O3 => qX ^ blockE e * (qX ^ blockE e - 1)⁻¹ * tRow β E σ
```

Faithfulness pins: `rowOf` is the landed II-R8 §2.3(iv) transcription (REUSED,
never redefined); the (O2′) leg's coefficient is PINNED = `kappa1 e` (the leaf's
"coefficient pinned = κ₁"); the (O3) scalar is the landed `gramOver_o3scale`
shape. `E.idx : Type` + `Fintype` matches the finite exit roster; a Finset-based
variant is REJECTED (comp needs a Π-type over per-F tuple length).

**D2 (carriers `REWitness`/`MassFacts`) — REVISION 2 form (Codex criticals
1/2/3/4 folded; RE-PROBED at HEAD, see §4.0).** Verbatim:

```lean
/-- (RE) at the corpus carrier: re-entrant booking; ROW-INDEXED canonical
    rows tied to the member's entry roster; L4 descent. See the no-α
    adjudication (δ4) below — this witness carries (RE)'s OPERATIVE content
    at the corpus granularity, with the compilation choices displayed. -/
structure REWitness {n : ℕ} (T : BnMember n) where
  exits : ℕ → ExitData n
  handoff_lt : ∀ e, ∀ F : (exits e).idx, ∀ x ∈ (exits e).handoff F, x.1 < e
  booking_reentrant : T.booking ≠ Booking.O2
  trow_canonical : ∀ e (he : 2 ≤ e), (T.blocks e he).trow = tRow T.β (exits e)
  row : ℕ → SplittingType n → Qq
  row_eq_displayed : ∀ e, 2 ≤ e → e ≤ n → ∀ σ,
    row e σ = displayedRow T.booking e T.β (exits e) σ
  row_mem_entries : ∀ e σ, 2 ≤ e → e ≤ n → row e σ ∈ T.entries e

/-- The M1 shadow at the member: (EXM) + (BASE) + regularity + (MNN).
    NOT (RE) clauses. -/
structure MassFacts {n : ℕ} (T : BnMember n) (W : REWitness T) : Prop where
  base_total : ∀ e ≤ 1, (∑ σ : SplittingType n, T.β e σ) = 1
  base_nonneg : ∀ e ≤ 1, ∀ σ (q₀ : ℚ), 2 ≤ q₀ →
    ∀ h : T.β e σ ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨T.β e σ, h⟩
  mass_complete : ∀ e, 2 ≤ e → e ≤ n →
    (∑ F : (W.exits e).idx, (W.exits e).mass F) = 1 - kappa0 e - kappa1 e
  mass_memRcyc : ∀ e, ∀ F : (W.exits e).idx, MemRcyc ((W.exits e).mass F)
  mass_nonneg : ∀ e, ∀ F : (W.exits e).idx, ∀ q₀ : ℚ, 2 ≤ q₀ →
    ∀ h : (W.exits e).mass F ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨(W.exits e).mass F, h⟩
```

REVISION 2 field notes: `row`/`row_eq_displayed`/`row_mem_entries` land the
(RE) row-form clause ON THE MEMBER'S CARRIED ROWS (Codex critical 2: pinning
only `BlockPresentation.trow` missed the family-(iv) displayed rows with their
O2′/O3 adjustments "and nothing else"); the residual granularity gap is
DISPLAYED — `BnMember.entries` is an un-indexed `Finset`, so `row_mem_entries`
is the strongest member-side tie the corpus carrier admits, and the σ-indexed
identification of REALIZED table rows with `row` stays route-a/route-b
territory (never claimed here). `base_nonneg`/`mass_memRcyc` complete the B1
input roster (criticals 3/4; `mass_memRcyc` is discharge-cheap at the intended
member: masses are `massPatt`/`massPoly` = Gram entries — `gram_massPatt`/
`gram_massPoly` + `Gram.memRcyc`, all landed).

**(δ4) The no-α adjudication (REVISION 2, folding Codex critical 1 — the
compilation choice DISPLAYED, never silent).** The corpus `BnCoordinates`
carries an `allocation` COORDINATE on every member (II-R12's raw data), so
"(RE): the member carries NO allocation datum at any block" CANNOT compile as
field-absence. Its compilation here is the ROW-FORM pair
`row_eq_displayed` + `trow_canonical`: the member's carried rows equal the
canonical assembly with ONLY the displayed booking adjustments — any
α-adjustment term (`t + α·q^{−E}`, the `gramOver_allocAdjust` shape) would
refute the equality, so α-freeness of the ROWS is a consequence, while the
inert coordinate remains as data. WARRANT for this reading: the leaf's own
display "(RE) states everything the proof uses", and every (RE) consumption
in the leaf (M2's proof step, (ROW-Σ)'s step (ii)) reads exactly the row
forms + booking, never the coordinate's absence. HONESTY RESIDUE: the (RE)
sentence is nonetheless STRONGER as worded (a member could carry a spurious
α that feeds nothing); a consumer needing the literal no-datum clause must
add it at the instance — displayed, not smuggled. `REWitness` therefore
carries (RE)'s OPERATIVE content; the blueprint's r1 claim "types the (RE)
conjunction exactly" is WITHDRAWN in favor of this display. The
displayedRow tie (that the member's PRESENTED per-booking rows are
`displayedRow`) is definitional at (O1) (`trow_canonical`) and enters R2 through
`displayedRow` itself — the O2′/O3 presented-row conformance at a REALIZED table
is route-a/route-b territory (clause-4-class), NOT smuggled into D2.

### 4.3 Wave 1 — kernels (`Kernels.lean`; fully parallel)

| unit | verbatim statement (probed) | difficulty | proof route |
|---|---|---|---|
| **K1** | `theorem memRcyc_mem_OKat {f : Qq} (hf : MemRcyc f) {q₀ : ℚ} (hq : 2 ≤ q₀) : f ∈ OKat q₀` | MED | `MemRcyc.eq_div` → `RatFunc.denom_div_dvd` → `cycS_eval_pos` (the `MemRcyc.definedAt` skeleton retargeted to the `OKat` carrier; `mem_OKat_iff`) |
| **K2a** | `theorem bnMember_entries_mem_OKat {n : ℕ} (T : BnMember n) : ∀ e, ∀ g ∈ T.entries e, ∀ q₀ : ℚ, 2 ≤ q₀ → g ∈ OKat q₀` | EASY | `T.entries_memRcyc` + K1 |
| **K2b** | `theorem bnMember_beta_mem_OKat {n : ℕ} (T : BnMember n) : ∀ e σ, ∀ q₀ : ℚ, 2 ≤ q₀ → T.β e σ ∈ OKat q₀` | EASY | `beta_memRcyc T.hbase T.blocks` + K1 |
| **K3** | `theorem evalAt_inv {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀) (hfi : f⁻¹ ∈ OKat q₀) (hne : evalAt q₀ ⟨f, hf⟩ ≠ 0) : evalAt q₀ ⟨f⁻¹, hfi⟩ = (evalAt q₀ ⟨f, hf⟩)⁻¹` | MED | f = 0 corner (then f⁻¹ = 0, both sides 0 — contradiction with hne; handle via `by_cases`); else `map_mul` on f·f⁻¹ = 1, `eq_inv_of_mul_eq_one_left` |
| **K4** | `theorem sum_rowOf {n : ℕ} (β : ℕ → SplittingType n → Qq) (m : Qq) (H : List (ℕ × ℕ+)) (comp : ((i : Fin H.length) → SplittingType n) → SplittingType n) : (∑ σ : SplittingType n, rowOf β m H comp σ) = m * ∏ i : Fin H.length, (∑ σ' : SplittingType n, powSubst (H.get i).2 (β (H.get i).1 σ'))` | MED | unfold `rowOf`; `Finset.sum_fiberwise` (comp total over `Finset.univ`) collapses the σ-sum of filtered sums to the full tuple sum; `Finset.mul_sum` + `Finset.prod_univ_sum` (pi-type distributivity) |

K1–K3 also serve PACK-iii/PACK-i directly; K4 is R1's step-1 engine. PACK-iii is
DISCHARGED at the 𝔅_n side when K2a/K2b land (§2.4).

### 4.4 Wave 2 — the skeleton (`RowSigma.lean`)

| unit | statement (probed shape; hypotheses split per D2's authoring split) | difficulty |
|---|---|---|
| **R1** | `theorem rowSigma_solved {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W) : ∀ e, e ≤ n → (∑ σ : SplittingType n, T.β e σ) = 1` | HARD (the §3 induction; `Nat.strong_induction_on`; consumes K4, `kappa_add`, `hblockU`, `hu.1`, `Booking.solveU` re-entrant branch via `booking_reentrant`) |
| **R2** | per-booking totals, three theorems (O1/O2r/O3), e.g. `theorem rowSigma_displayed_O1 … (hb : T.booking = Booking.O1) {e : ℕ} (he2 : 2 ≤ e) (hen : e ≤ n) : (∑ σ : SplittingType n, displayedRow T.booking e T.β (W.exits e) σ) = 1 - kappa0 e - kappa1 e` (probed at O1; O2r concludes `= 1 - kappa0 e`; O3 concludes `= 1 - (qX - 1) * (qX ^ blockE e - 1)⁻¹`) | MED (given R1; `ring`/`field_simp` + `kernel_ne_zero` ingredients) |
| **R3** | `theorem rowSigma_eval {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W) {q₀ : ℚ} (hq : 2 ≤ q₀) {e : ℕ} (he : e ≤ n) : (∑ σ : SplittingType n, evalAt q₀ ⟨T.β e σ, bnMember_beta_mem_OKat T e σ q₀ hq⟩) = 1` | MED (subring-coercion sum + `map_sum` + R1) |

### 4.5 Wave 3 — (PACK-ii) (`Bdd.lean`)

| unit | statement | difficulty |
|---|---|---|
| **B1** | [REVISION 2, folding Codex critical 3 — range condition added, base/regularity inputs now `MassFacts` fields; RE-PROBED] `theorem beta_eval_nonneg {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W) : ∀ e, e ≤ n → ∀ σ (q₀ : ℚ), 2 ≤ q₀ → ∀ h : T.β e σ ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨T.β e σ, h⟩` — the pool quantifier sits INSIDE the induction (the leaf §2A.2's own display: "uniform in q₀ … so the induction hypothesis applies at the child pools q₀^{D_i}"; a fixed-q₀ outer binder would break the IH at the base-changed legs); `e ≤ n` is REQUIRED (`mass_complete` supplies nothing above n — the r1 unrestricted form was unprovable); the e ≤ 1 base fires `base_nonneg`, and per-stratum regularity fires `mass_memRcyc` + K1 | HARD (strong induction on e with q₀ generalized: `hsolve` → nonneg quotient of nonneg t (masses (MNN) × legs via IH THROUGH `powSubst_evalAt` at the child pool `q₀ ^ (D_i : ℕ)` — `2 ≤ q₀ → 2 ≤ q₀^D` by `le_self_pow`-class arithmetic, D ≥ 1) by positive pivot (P0 — Wave 1 per the REVISION-2 reorder)) |
| **B2** | `theorem beta_eval_mem_Icc {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W) {q₀ : ℚ} (hq : 2 ≤ q₀) {e : ℕ} (he : e ≤ n) (σ : SplittingType n) (h : T.β e σ ∈ OKat q₀) : evalAt q₀ ⟨T.β e σ, h⟩ ∈ Set.Icc (0 : ℚ) 1` | EASY (B1 + R3: one term of a nonneg sum totalling 1) |

### 4.6 Wave 4 — (PACK-i) block form (`PackI.lean`)

| unit | statement | difficulty |
|---|---|---|
| **P0** | [REVISION 2: MOVED to Wave 1 (B1 consumes it — Codex gap 13) and split; both halves RE-PROBED] `theorem solveU_mem_OKat {e : ℕ} (he : 2 ≤ e) (b : Booking) {q₀ : ℚ} (hq : 2 ≤ q₀) : b.solveU e ∈ OKat q₀` and `theorem solveU_eval_pos {e : ℕ} (he : 2 ≤ e) (b : Booking) (hb : b ≠ Booking.O2) {q₀ : ℚ} (hq : 2 ≤ q₀) (h : b.solveU e ∈ OKat q₀) : 0 < evalAt q₀ ⟨b.solveU e, h⟩` | MED (u = 1 − q·q^{−E}; eval = 1 − q₀^{1−E} ≥ 3/4 via `blockE_ge_three` arithmetic; the Corollary-D scalar margin) |
| **P1** | [REVISION 2: PROBED at the r2 round — the r1 PROBE-OWED tag CLEARED; redundant `hui` binder dropped at probe] `theorem beta_eval_solve {n : ℕ} (T : BnMember n) {e : ℕ} (he : 2 ≤ e) {q₀ : ℚ} (hq : 2 ≤ q₀) (σ : SplittingType n) (hβ : T.β e σ ∈ OKat q₀) (ht : (T.blocks e he).trow σ ∈ OKat q₀) (hu : (T.blocks e he).u ∈ OKat q₀) (hne : evalAt q₀ ⟨(T.blocks e he).u, hu⟩ ≠ 0) : evalAt q₀ ⟨T.β e σ, hβ⟩ = (evalAt q₀ ⟨(T.blocks e he).u, hu⟩)⁻¹ * evalAt q₀ ⟨(T.blocks e he).trow σ, ht⟩` — solve-evaluation commutation; membership binders dischargeable via K1 + `hu`/`MemRcyc.mul` at call sites | MED (rewrite `hsolve`, `map_mul` of `evalAt`, K3 — the u⁻¹ membership K3 needs is supplied inside the proof from `hu.2.2` + K1) |

### 4.7 Wave 5 — conformance (`Conform.lean`)

| unit | statement | difficulty |
|---|---|---|
| **C1** | `packOfMember`/`refOfMember`/`packOfMember_corr`: probed skeleton `noncomputable def packOfMember {n : ℕ} (T : BnMember n) (rowsOf : ℕ → Finset Qq) : ValueSide.AssembledPack n` with `Row := (e : Finset.Icc 1 n) × {g : Qq // g ∈ rowsOf e.1}` (instR = `Sigma.instFintype` route), `entry r = r.2.1`, `blockOf r = r.1.1`; at call sites `rowsOf := T.entries`; `refOfMember` reads the SAME data into `PackReference n C P`; `packOfMember_corr : PackCorrespondence n C (packOfMember T T.entries) (refOfMember …)` by `rfl`-fields | MED (the Fintype instance is the only non-rfl content) |
| **C2** | `mkREMember` — route-b builder [REVISION 2 duty list per Codex critical 2]: from `(C : BnCoordinates n)` re-entrant-booked + per-block `ExitData` + the solve data, produce `(T : BnMember n) × REWitness T` where the builder DEFINES `row e σ := displayedRow …` and puts the constructed rows into the built `entries` roster — so `trow_canonical`/`row_eq_displayed` are `rfl`-class and `row_mem_entries` is discharged by construction, never assumed | MED/HARD (assembling `BlockPresentation` needs the GramOver walk — reuse `gramOver_rowOf`/`GramOver.finsetSum`, landed II-R8/II-R3; plus the entries-roster duty) |
| **C3** | [REVISION 2, folding Codex critical 5 — RE-PROBED] `H5PackTyped` bundle, now over `(T : BnMember n) (W : REWitness T) (M : MassFacts T W)` (the ACTUAL witnesses, not `Nonempty` — B2's consumption needs them), with FIVE fields: `corr : PackCorrespondence n C P R` · `ref_reads_member : ∀ r : P.Row, R.intendedEntry r ∈ T.entries (R.intendedBlock r)` (the T↔R tie the r1 form lacked — an ENTRY-LEVEL tie; the σ-keyed identification stays route territory, displayed) · `wsh` (K2a shape) · `bdd` (B2 shape, `e ≤ n`-scoped) · `solve_interp` (P1 shape — the PACK-i block form, absent in r1) + consumption theorem `h5PackTyped_laws`. DEDUP/OWNERSHIP (folding gap 12): `H5PackTyped` is chartered as THE FIELD-REFINEMENT TARGET for BP_VI's `h5_pack` (bare Prop at ROOT-REVISION-5 sync); at refinement time BP_VI lands the equivalence/migration theorem and owns the swap — H5 never edits `Hypotheses.lean`; the bundle duplicates NO law (every field is a NAMED earlier unit's conclusion shape) | EASY |
| **C4** | n = 2 instance gate — E-PHASE-GATED spec: adjudicate carrier choice against the M04 F1 fence (device chain FENCED from value claims; the honest reference = the S-area real pack), then instantiate `packOfMember`-side `PackCorrespondence` at n = 2 by `decide`/`rfl` on the finite table | HARD/DATA, gated |
| **C5** | n = 3 route-a spec (NO Lean unit lands now): the OL-O12-2 transcription-and-correspondence pass EXTENDED by the named per-row booking-profile duty (design §3.3 (route-a) verbatim) — executable when n = 3 tables land; numeric precursor RESUM-n3 65/65 on record | BLOCKED/DATA |

### 4.8 Wave order and parallelism

```
W0: D1 → D2                        (one prover; Codex statement-audit gate)
W1: K1 ∥ K3 ∥ K4 ∥ P0;  K2a/K2b after K1   (three-four provers)
    [REVISION 2: P0 MOVED to W1 — Codex gap 13: B1 consumes P0's pivot
     positivity, so P0 must precede W3, and it is kernel-independent]
W2: R1 → R2 ∥ R3                   (one prover for R1; R2/R3 parallel after)
W3: B1 → B2                        (after W2 AND P0; one prover)
W4: P1                             (after W1; one prover)
W5: C1 ∥ C3 after W0; C2 after W0; C4 gated; C5 blocked
```
Total: 17 chartered declarations across 6 files (P0 split into
`solveU_mem_OKat` + `solveU_eval_pos` at the r2 probe): 15 provable at HEAD,
1 E-phase-gated (C4), 1 blocked-data (C5). [REVISION 2 sync of the r1 count.]

---

## 5. Numerics / falsifier gates (flags, never substitutes)

* **R1/R2 gate:** n = 2 symbolic totals against the landed N2 solve values
  (Σ_σ β₂(σ) = 1; per-booking S₂ = Φ^{(booking)} at q₀ ∈ {2,3,4,5}) — a
  `#eval`-class check in the prover's scratch, plus the standing
  `verification/` RESUM-n3 65/65 record for n = 3.
* **B1 gate:** spot evaluations of the n = 2 β at q₀ = 2,3 lie in [0,1]
  (already implied by the O-11 falsifier record; re-run cheaply).
* **(EXM) sanity (pre-follow-on):** at n = 2, Σ_F m(F) = 1 − κ₀ − κ₁ against
  the level-1 census (M08's 46-strata machine-checked table is the n = 3 analog).

## 6. What this blueprint does NOT discharge (the honest residue, displayed)

1. **Clause 4 at the consumed instance** — the realized-tables ↔ intended-member
   identification (OL-O12-2 data half at n = 3; O-14d population at general n).
   C1/C2 make it a finite executable check; they do not execute it.
2. **(PACK-iv) at the consumed instance** — same routes; D2/C2 are the carrier
   and builder, not the data pass.
3. **The chain-vocabulary (PACK-i/ii/iii)** — the real general-n `RS4Chain`
   instance construction (its `rsh_interp`/`r_bdd`/`wsh_ok` fields will consume
   P1/B2/K2a-K2b); owner: the D-11/O-14d instance-population unit.
4. **(EXM)/(BASE)/(MNN) at the intended member** — the M1/census shadow
   (M08-layer follow-on, named in §3).
5. **ROOT §3.1 row text** — untouched; (H5) stays [M] as displayed until the
   routes execute and a ROOT revision re-prices it.
6. **`Scaffold/Hypotheses.lean`** (BP_VI-owned, synced at ROOT REVISION 5 —
   `h5_pack` is a bare Prop and the file predates PACK-i..iv): the field
   refinement toward `H5PackTyped` is BP_VI's sync duty; H5 does not edit it.
   FLAGGED to the BP_VI owner with this blueprint.

---

## 7. Codex adversarial review + REVISION 2 (the fold record)

**The pass (the directive's required verification):** one adversarial Codex
review, fresh context, prompt = the quote-and-classify charge + this blueprint
(r1 text) + the authoritative sources pasted (the §3.1 (PACK) row, Theorem M2
(r4)'s (RE) display + consumed-instance note, leaf §2A.1–2A.3, design §3.5 +
route display, and the landed corpus declarations `BlockPresentation`/`rowOf`/
`kappa0/1`/`solveU`/`BnCoordinates`/`BnMember`). Verdict on r1: **REJECT — 5
CRITICAL + 8 GAP**. Full findings archived VERBATIM at
`lean/notes/openmath/H5_bp_review.md`. Key POSITIVE finding (7): "Conditional
on symbolic EXM, BASE, `handoff_lt`, `trow_canonical`, `hsolve`, `hblockU`,
and `hu.1`, the R1 induction is sound. The three R2 totals also agree with the
leaf's Φ values" — the mathematical core CONFIRMED; every finding is at the
statement/display level. REVISION 2 = this fold; every REVISION-2-changed Lean
statement re-probed at HEAD (§4.0 r2 probe: 4 sorries, 0 errors).

### Disposition table (finding → adjudication → repair location)

| # | class | finding (compressed) | adjudication | repair |
|---|---|---|---|---|
| 1 | CRIT | `REWitness` does not encode "no allocation datum" (coordinate exists on every member; omission ≠ absence) | VALID — the r1 "types (RE) exactly" claim overclaimed; the operative-content compilation must be argued, not asserted | (δ4) adjudication display (§4.2): no-α compiles to the row-form pair, warrant = the leaf's "(RE) states everything the proof uses"; literal no-datum clause displayed as at-instance residue; "exactly" WITHDRAWN (§2.5 + §4.2 rewordings) |
| 2 | CRIT | `trow_canonical` pins only the block presentation's aggregate, not the member's family-(iv) DISPLAYED rows with O2′/O3 adjustments "and nothing else" | VALID — the r1 witness missed the row-level clause | `REWitness` gains `row`/`row_eq_displayed`/`row_mem_entries` (re-probed); the Finset-granularity residue displayed; `mkREMember` duty list updated (§2.5, §4.7 C2) |
| 3 | CRIT | B1 unprovable: no `e ≤ n` (mass_complete supplies nothing above n) + base nonneg missing | VALID (the range condition was a genuine statement bug; base_nonneg had been an E-phase hedge) | B1 restated with `e ≤ n`; `base_nonneg` now a `MassFacts` FIELD; re-probed (§4.4/§4.5) |
| 4 | CRIT | B1 lacks mass regularity (no link from `ExitData.mass` to `MemRcyc`/`OKat`) | VALID (pre-folded by the lead minutes before the review landed — now completed) | `mass_memRcyc` now a `MassFacts` FIELD (re-probed); discharge-cheap note retained (§4.2) |
| 5 | CRIT | `H5PackTyped` cannot express the package: no PACK-i field, no T↔R tie, `Nonempty (REWitness)` too weak for B2, no `MassFacts` | VALID | Bundle restated over `(T, W, M)` with five fields incl. `solve_interp` (PACK-i) and `ref_reads_member` (entry-level T↔R tie; σ-keyed tie displayed as route territory); re-probed (§4.7 C3) |
| 6 | GAP | "honest maximal scope" unsupported; door-table "YES" readable as ROOT retirement | VALID | PACK-ii cell reworded: CONDITIONAL YES, C6 motivates the restriction but does not certify minimality; intended-member witnesses open (§1) |
| 7 | GAP | symbolic (EXM) stronger than the leaf's per-evaluation mass input; derivation absent; child-pool bookkeeping "disappears" only for R1, not B1 | VALID (and finding 7 CONFIRMS the R1/R2 core) | STRENGTH NOTE + chartered follow-on F3 (infinite-agreement lemma) added to §3; B1's uniformity was already folded (pool quantifier inside the induction) |
| 8 | GAP | PACK-iii "full discharge" lacks the weight/shape-series roster identification + chain-field transport | VALID | §2.4 + door table narrowed to the two proved collections; roster identification + chain seam displayed as open (subring-closure remark added) |
| 9 | GAP | C1 tautological; Finset `Row` collapses equal entries — "entry-for-entry" is positional at source | VALID | §2.1 route-b caveats (i)/(ii): scaffolding-not-transfer + the multiset/position-indexed refinement flagged as E-phase option; door-table cell reworded |
| 10 | GAP | "route-a n ≤ 3" misstates the design (route-a is n = 3 ONLY; n = 2 is evidence, not a route) | VALID | Door-table clause-4 route cell reworded; C4 remains an instance GATE, not route-a |
| 11 | GAP | O2 junk branch: public `displayedRow` type carries no guard — interface risk | VALID (risk, not falsity) | (δ3) extended with the GUARDED-API DISCIPLINE line: every consumer keyed by booking equality / `booking_reentrant` |
| 12 | GAP | dedup incomplete: `H5PackTyped` vs `PackCorrespondence`/`h5_pack` unadjudicated; ExitData↔BnCoordinates left as bare flag | VALID | C3 row: bundle = BP_VI's field-refinement TARGET, equivalence/migration theorem at refinement time, BP_VI owns the swap; (δ2): compatibility proposition chartered as F1; the InstancePin tie chartered as F2 (§2.1) |
| 13 | GAP | wave order backward (B1 ← P0 with P0 in W4); §4.0 "every statement probed" contradicted P1's PROBE-OWED | VALID | P0 moved to Wave 1 (split into two probed halves); §4.0 rewritten as the two-round probe record; P1 probed at r2, tag cleared |

**Follow-on units chartered by this fold (not in the wave plan; owners named):**
F1 (ExitData↔BnCoordinates compatibility — BP_II-side), F2 (PackCorrespondence
↔ InstancePin tie — second-lander), F3 ((EXM) from per-pool agreement — the
census follow-on's entry lemma).

**Post-fold status: READY** — wave plan executable as §4.8 (15 provable-at-HEAD
units, C4 gated, C5 blocked-data); the residues of §6 unchanged in kind, now
with the Codex-sharpened displays. A confirming second Codex pass on THIS
(REVISION 2) text is the standard next gate before prover fan-out; it rides
the fan-out dispatch, not this blueprint-only unit.
