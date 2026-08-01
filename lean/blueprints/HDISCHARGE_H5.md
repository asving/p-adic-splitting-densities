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
| clause 4 | **CONF** | route-b constructor (+ route-a n ≤ 3 data instances) | `packOfMember`/`refOfMember` + by-construction `PackCorrespondence` (unit C1); n = 2 instance gate (C4, E-phase-gated); n = 3 = BLOCKED/DATA (C5) | NO — retires only when executed AT THE CONSUMED INSTANCE (OL-O12-2 data pass at n = 3 / O-14d population at general n) |
| (PACK-i) | **PROVE** (block form) + seam note (chain form) | the member's solve β = u⁻¹·t commutes with `evalAt` at every q₀ ≥ 2 (pivot ≠ 0 by margins) | units P0/P1 (PROVED at the 𝔅_n block presentation) | block form YES at the 𝔅_n side; the K2 chain-vocabulary form (`RS4Chain.rsh_interp` at the real instance) rides the chain-instance seam (§2.2) |
| (PACK-ii) | **PROVE at (RE)+MassFacts members** | the symbolic (ROW-Σ) skeleton (Σ_σ β_e = 1) + the nonneg induction ⟹ each value ∈ [0,1] | units R1/R3/B1/B2 | YES at (RE)+MassFacts members — the (RE) dependence is REAL (owed-pass C6's arbitrary-α counterexample), so this is the honest maximal scope |
| (PACK-iii) | **PROVE** | `MemRcyc → OKat q₀` bridge + the PROVED Theorem 2 (`BnMember.entries_memRcyc`, landed II-R13) | units K1/K2 | YES at the 𝔅_n side (every member entry/leg, every q₀ ≥ 2) — the cheapest full discharge in the group |
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
BP_IV pair; unit C3's bundle carries a slot where II-G5's `InstancePin` plugs in
when it lands (opaque-parameter pattern, the BP_IV REVISION-3 precedent). H5 does
NOT declare `InstancePin` (owner: BP_II).

**Route-b (general n).** Define the pack READ OFF the member
(`packOfMember T := the Σ-type table over T.entries`) and the reference reading
the SAME member (`refOfMember`); `PackCorrespondence` then holds by `rfl`-class
proof (unit C1). Honest residue, displayed: this proves "the constructed pack
conforms to the member it was constructed from" — the LAW-TRANSFER machinery.
What remains open is the identification of the REALIZED corpus tables (the
classifier-built pack that Steps 17/18 actually consume) with `packOfMember` of
the intended member: that is exactly OL-O12-2's data half / the O-14d population
duty, and it STAYS the row's open content until executed (route-a at n = 3;
O-14d construction at general n). No unit here claims it.

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
`BnMember`). This discharges (PACK-iii)'s content at the 𝔅_n rows in full: every
row entry AND every solved leg lies in the evaluation-regular subring at every
q₀ ≥ 2 — prime powers included (they satisfy 2 ≤ q₀). [D-6 in the ROOT display is
the K3 consumption partner (evalAt's ring-hom laws), already landed as
`MovesS.evalAt`; no new obligation.]

### 2.5 (PACK-iv) sem_alloc — CONF (carrier + builder now; data/population later)

**Carrier (unit D2):** `REWitness T` types the (RE) conjunction exactly — the
member's booking is re-entrant (`T.booking ≠ Booking.O2`); the per-block
family-(iv) aggregate is the canonical assembly over per-exit-stratum data
(`trow_canonical`: the landed `BlockPresentation.trow` EQUALS `tRow` built from
`rowOf` — the corpus's own §2.3(iv) transcription, II-R8); hand-offs descend
(L4 clause). "No allocation datum" is carried STRUCTURALLY: `REWitness` mentions
no `AllocDatum`, and `trow_canonical` pins the rows to the α-free form — an
α-adjusted row would refute it. The (O2′)/(O3) adjustments live in
`displayedRow` (unit D1), pinned to the leaf's three displayed forms.
**Faithfulness deltas, displayed (trust surface for the Codex pass):**
(δ1) the corpus `BookingSystem` carries ONE booking for the whole member, so
"EVERY block booked re-entrantly" compiles to the single-field disequality —
faithful at the corpus's own granularity (BP_II transcribed 𝔅_n that way);
(δ2) `BnCoordinates.handoffs/composition` are per-BLOCK aggregates while the
§2.3(iv) display is per-EXIT-STRATUM (H(F), comp_F) — `ExitData` (unit D1) is
the per-stratum refinement the row-form needs; the D1↔`BnCoordinates` seam is
flagged for the next BP_II touch, NOT silently unified here; (δ3) the O2 branch
of `displayedRow` is a guarded placeholder (= the unadjusted t), NEVER consumed
under `booking_reentrant` — the same junk-value-plus-guard convention as
`Booking.kernel` at e ≤ 1.

**Builder (unit C2, route-b's Lean face):** `mkREMember` — from re-entrant-booked
coordinates with rows DEFINED canonically, produce the `BnMember` together with
its `REWitness`, fields `rfl`-discharged. When the O-14d population constructs
the intended member through this builder, (PACK-iv) at that member holds by
construction — design §3.3 (route-b) verbatim. Route-a (n = 3) stays a data
pass: unit C5's spec names the per-row duty (verify each sealed block's booking
against the (O3) forms and each row against §2.3(iv) + the displayed scaling) —
executable only when n = 3 tables land in Lean; BLOCKED/DATA.

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

Every §4 statement below was probed VERBATIM (sorry-bodied) against HEAD
`b314edc` in one file importing `Scaffold.O12.Family`, `Scaffold.ValueSide.Hyps`,
`MovesS.PowSubstOK`: **8 sorry warnings, ZERO errors** (probe file deleted after
recording; two fixes folded during probing — `ValueSide.` qualification on
`AssembledPack` outside the `open`, and `rowsOf : ℕ → Finset Qq` binder typing in
C1). Statement shapes are therefore ELABORATION-SAFE at HEAD; provers may adjust
implicit binders/instance arguments per the standing BP_II §1 rule, never
mathematical content.

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

**D2 (carriers `REWitness`/`MassFacts`).** Verbatim (probed as one structure;
SPLIT at authoring time into the (RE)-exact witness and the M1-shadow — field
types byte-identical to the probe, so elaboration-safe):

```lean
/-- (RE) typed exactly: re-entrant booking; canonical α-free rows; L4 descent. -/
structure REWitness {n : ℕ} (T : BnMember n) where
  exits : ℕ → ExitData n
  handoff_lt : ∀ e, ∀ F : (exits e).idx, ∀ x ∈ (exits e).handoff F, x.1 < e
  booking_reentrant : T.booking ≠ Booking.O2
  trow_canonical : ∀ e (he : 2 ≤ e), (T.blocks e he).trow = tRow T.β (exits e)

/-- The M1 shadow at the member: (EXM) + (BASE) + (MNN). NOT (RE) clauses. -/
structure MassFacts {n : ℕ} (T : BnMember n) (W : REWitness T) : Prop where
  base_total : ∀ e ≤ 1, (∑ σ : SplittingType n, T.β e σ) = 1
  mass_complete : ∀ e, 2 ≤ e → e ≤ n →
    (∑ F : (W.exits e).idx, (W.exits e).mass F) = 1 - kappa0 e - kappa1 e
  mass_nonneg : ∀ e, ∀ F : (W.exits e).idx, ∀ q₀ : ℚ, 2 ≤ q₀ →
    ∀ h : (W.exits e).mass F ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨(W.exits e).mass F, h⟩
```

`REWitness` carries the (RE) conjunction and NOTHING else ("no allocation
datum" = structural: no `AllocDatum` field, rows pinned α-free by
`trow_canonical`); `MassFacts : Prop` carries the leaf's M1-side inputs.
E-PHASE COMPLETION NOTE (lead's own probe-review): `MassFacts` additionally
needs (i) `base_nonneg` (see B1) and (ii) `mass_memRcyc : ∀ e F, MemRcyc
((W.exits e).mass F)` — B1's decomposition of evalAt(t) into per-stratum terms
needs each summand evaluation-regular, and t's own regularity (via `htrow`)
does not distribute; at the intended member the field is discharge-cheap
(masses are `massPatt`/`massPoly` = Gram entries: `gram_massPatt`/
`gram_massPoly` + `Gram.memRcyc`, all landed). Fields are additions to the
PROBED shapes (same genre as the probed `mass_nonneg`), flagged for the D2
prover's re-probe.
IMPORTANT no-α reading (δ4): the corpus `BnCoordinates` carries an
`allocation` COORDINATE on every member (II-R12's raw data), so "(RE): carries
NO allocation datum" CANNOT compile as field-absence on the coordinates; its
faithful compilation is `trow_canonical` — the presented rows contain no
α-adjustment term (an α-adjusted member would refute the equality with the
canonical `tRow`). The (O2)-booking's α consumption is fenced by
`booking_reentrant`. The
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
| **B1** | `theorem beta_eval_nonneg {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W) : ∀ e σ, ∀ (q₀ : ℚ), 2 ≤ q₀ → ∀ h : T.β e σ ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨T.β e σ, h⟩` — the pool quantifier sits INSIDE the induction (the leaf §2A.2's own display: "uniform in q₀ … so the induction hypothesis applies at the child pools q₀^{D_i}"; a fixed-q₀ outer binder would break the IH at the base-changed legs — provers must induct on e FIRST, keeping ∀ q₀ in the motive). PLUS a base-nonneg field decision at E-phase: e ≤ 1 nonneg is NOT derivable from `MassFacts` as displayed; add `base_nonneg` to `MassFacts` (preferred; block 1 = single verdict β = 1 at the intended member) | HARD (strong induction on e with q₀ generalized: `hsolve` → nonneg quotient of nonneg t (masses (MNN) × legs via IH THROUGH `powSubst_evalAt` at the child pool `q₀ ^ (D_i : ℕ)` — `2 ≤ q₀ → 2 ≤ q₀^D` by `le_self_pow`-class arithmetic, D ≥ 1) by positive pivot (P0)) |
| **B2** | `theorem beta_eval_mem_Icc {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W) {q₀ : ℚ} (hq : 2 ≤ q₀) {e : ℕ} (he : e ≤ n) (σ : SplittingType n) (h : T.β e σ ∈ OKat q₀) : evalAt q₀ ⟨T.β e σ, h⟩ ∈ Set.Icc (0 : ℚ) 1` | EASY (B1 + R3: one term of a nonneg sum totalling 1) |

### 4.6 Wave 4 — (PACK-i) block form (`PackI.lean`)

| unit | statement | difficulty |
|---|---|---|
| **P0** | `theorem solveU_eval_pos {e : ℕ} (he : 2 ≤ e) (b : Booking) (hb : b ≠ Booking.O2) {q₀ : ℚ} (hq : 2 ≤ q₀) : ∀ h : b.solveU e ∈ OKat q₀, 0 < evalAt q₀ ⟨b.solveU e, h⟩` (+ the membership itself, `solveU_mem_OKat`) | MED (u = 1 − q·q^{−E}; eval = 1 − q₀^{1−E} ≥ 3/4 via `blockE_ge_three` arithmetic; the Corollary-D scalar margin) |
| **P1** | `theorem beta_eval_solve {n : ℕ} (T : BnMember n) {e : ℕ} (he : 2 ≤ e) {q₀ : ℚ} (hq : 2 ≤ q₀) (σ : SplittingType n) : ∀ (hβ : T.β e σ ∈ OKat q₀) (ht : (T.blocks e he).trow σ ∈ OKat q₀) (hu : (T.blocks e he).u ∈ OKat q₀) (hui : (T.blocks e he).u⁻¹ ∈ OKat q₀) (hne : evalAt q₀ ⟨(T.blocks e he).u, hu⟩ ≠ 0), evalAt q₀ ⟨T.β e σ, hβ⟩ = (evalAt q₀ ⟨(T.blocks e he).u, hu⟩)⁻¹ * evalAt q₀ ⟨(T.blocks e he).trow σ, ht⟩` — solve-evaluation commutation; membership binders dischargeable via K1 + `hu`/`MemRcyc.mul` at call sites | MED (rewrite `hsolve`, `map_mul` of `evalAt`, K3) — [NOT probed verbatim; assembled from probed K3 + landed fields; E-phase re-probe REQUIRED, tag PROBE-OWED] |

### 4.7 Wave 5 — conformance (`Conform.lean`)

| unit | statement | difficulty |
|---|---|---|
| **C1** | `packOfMember`/`refOfMember`/`packOfMember_corr`: probed skeleton `noncomputable def packOfMember {n : ℕ} (T : BnMember n) (rowsOf : ℕ → Finset Qq) : ValueSide.AssembledPack n` with `Row := (e : Finset.Icc 1 n) × {g : Qq // g ∈ rowsOf e.1}` (instR = `Sigma.instFintype` route), `entry r = r.2.1`, `blockOf r = r.1.1`; at call sites `rowsOf := T.entries`; `refOfMember` reads the SAME data into `PackReference n C P`; `packOfMember_corr : PackCorrespondence n C (packOfMember T T.entries) (refOfMember …)` by `rfl`-fields | MED (the Fintype instance is the only non-rfl content) |
| **C2** | `mkREMember` — route-b builder: from `(C : BnCoordinates n)` re-entrant-booked + per-block `ExitData` + canonically-DEFINED rows + the solve data, produce `(T : BnMember n) × REWitness T` with `trow_canonical := rfl`-class | MED/HARD (assembling `BlockPresentation` needs the GramOver walk — reuse `gramOver_rowOf`/`GramOver.finsetSum`, landed II-R8/II-R3) |
| **C3** | `H5PackTyped` bundle (probed): `structure H5PackTyped (n : ℕ) (C : UCarriers n) (P : AssembledPack n) (R : PackReference n C P) (T : BnMember n) : Prop where corr : PackCorrespondence n C P R; re_profile : Nonempty (REWitness T); wsh : …K2a-shape…; bdd : …B2-shape…` + consumption theorem `h5PackTyped_laws` unpacking to the four member conclusions; carries the II-G5 `InstancePin` plug-slot as an opaque-parameter comment until BP_II lands it | EASY |
| **C4** | n = 2 instance gate — E-PHASE-GATED spec: adjudicate carrier choice against the M04 F1 fence (device chain FENCED from value claims; the honest reference = the S-area real pack), then instantiate `packOfMember`-side `PackCorrespondence` at n = 2 by `decide`/`rfl` on the finite table | HARD/DATA, gated |
| **C5** | n = 3 route-a spec (NO Lean unit lands now): the OL-O12-2 transcription-and-correspondence pass EXTENDED by the named per-row booking-profile duty (design §3.3 (route-a) verbatim) — executable when n = 3 tables land; numeric precursor RESUM-n3 65/65 on record | BLOCKED/DATA |

### 4.8 Wave order and parallelism

```
W0: D1 → D2                       (one prover; Codex statement-audit gate)
W1: K1 ∥ K3 ∥ K4;  K2a/K2b after K1        (three provers)
W2: R1 → R2 ∥ R3                  (one prover for R1; R2/R3 parallel after)
W3: B1 → B2                        (after W2; one prover)
W4: P0 ∥ P1                        (after W1; one prover)
W5: C1 ∥ C3 after W0; C2 after W0; C4 gated; C5 blocked
```
Total: 16 chartered declarations across 6 files; 13 provable at HEAD, 1
E-phase-gated (C4), 1 blocked-data (C5), 1 probe-owed statement variant (P1).

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

