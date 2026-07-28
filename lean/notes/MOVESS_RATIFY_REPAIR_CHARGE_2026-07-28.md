# MovesS RATIFICATION-REPAIR CHARGE (2026-07-28, orchestrator-adjudicated)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Corpus: lean/LeanUrat/MovesS/
(88/95 proved; 7 seam-gated). Fresh-context Codex ratification (verdict text at
/tmp/leanratify_s/verdict.txt — READ IT FIRST) returned 5 crit / 0 gap; the orchestrator
accepted ALL FIVE after direct note reads (MOVES = lean/notes/MOVES_2026-07-24.md,
§S-RESUM = lines 11557–12577; the (ii-c) display at 12204–12218; halted-factor display
near the b_e^split clauses). Execute the repairs; keep the 88 proved units green; additive
except where a def change is specified EXACTLY. No git — the orchestrator commits.

## Ground rules
- Statement fence: existing theorem statements stay byte-identical unless a repair below
  explicitly restates them (S2 may force signature-neutral proof patches — statements
  themselves must not change; if a statement MUST change to stay true, STOP on that item
  and report the exact obstruction instead).
- Structure-field ADDITIONS to RS4Chain/RS1Bundle are allowed (that is the repair); every
  place constructing an instance must be updated (grep for the constructors; N2ReadOff's
  device is the main instance — keep it PROVED, it is a sealed gate).
- Do not touch other corpora. Build per module + full `lake build` at the end + Lean-core
  axiom spot-checks. Staged writes ≤4000 tokens/response. Docstrings cite note lines.

## S1 (wild-pool read-off gate not inherited) — ACCEPTED
Note 12204–12218: at every NON-all-active pool the evaluated object's q₀-value "equals the
active-subsystem solve there must pass BEFORE it may be read off"; a surviving pole is
(ii-c)'s FAIL. The corpus HAS the gate (Defs.lean `AVAgree`, 502–504, correctly typed) and
the all-active bundle (Interfaces.lean `ReadOffBundle`) carries it totally; but the
inherited-set record `legs_reg : ∀ p ∈ PrimePools, RegP …` supplies ONLY
`Nonempty (PoolHyp …)` (E0/ACT/inactive-vanish/entries) at consumed pools — no agreement
burden at the non-all-active ones. Repair:
(a) In Defs.lean add the consumed-leg agreement burden, β-side, mirroring AVAgree's shape:
    def LegAgree (T M RB hdc hK hdet) (βm : the measured β family) (q₀) : Prop :=
      ∀ e he τA σ' h_ent, AVAgree (the pool package at q₀) (blockSolve … e he τA σ')
        (bhatMeas … σ') τA — i.e. exactly ReadOffBundle.read's clause at ONE pool. Factor
    it so ReadOffBundle.read becomes (or is provably equal to) "∀ q₀ ∈ S, LegAgree …" —
    WITHOUT changing ReadOffBundle's fields (add a lemma, not a field change, if easier).
(b) In Interfaces.lean add to RS4Chain the typed field:
      legs_read : ∀ p : ℕ, (p : ℚ) ∈ PrimePools → ∀ δ ∈ consumedDeltas T F,
        ((p : ℚ) ^ (δ : ℕ)) ∉ allActivePools M →   -- the non-all-active (wild) pools
          LegAgree … ((p : ℚ) ^ (δ : ℕ))
    (the note's PER-POOL weakened (ii-c), quoted in the docstring: gate BEFORE read-off;
    junk-block determinants stay census-side, NOT required nonzero — say so.)
(c) Thread: every existing RS4Chain consumer keeps compiling (new field = new obligation
    at instances only). Update the N2 device instance (N2ReadOff/N2Det etc.): n = 2 pools
    are all-active (n2_pools_all suggests exactly this), so the new field discharges
    VACUOUSLY there — prove it, keep the gate green. If any OTHER instance exists, treat
    likewise.

## S2 (consumedDeltas over-collects halted members) — ACCEPTED (silent strengthening)
Note: halted members contribute FACTOR 1; β is evaluated only at block-state members; the
consumed δ's are those of legs b_e^split/RS.1-SH CONSUMES. Repair — the ONE def change:
in Defs.lean `deltaFactors` (line ~538) filter to continuing members:
    then (((T.odata e τ o).mem.filter (fun μ => μ.status.isRight)).map Member.δ).toFinset
Docstring: cite the halted-factor-1 display. Ripple: `nested_delta_mem` (U-16a3) and any
membership proofs — re-prove with the filtered def (memberships needed downstream are for
CONTINUING legs, which survive the filter; halted-δ memberships must NOT be needed — if
one IS needed somewhere, STOP on this item and report the consumer, because that would
mean the corpus genuinely evaluates β at a halted leg contra the note). RegP/legs_reg/
legs_read weaken accordingly (fewer pools) — instances get EASIER; consumers unaffected.

## S3 (J-RAT contract granularity) — ACCEPTED (type the per-cell interface; owner [1v])
PLAN-SYNC: deliverable = PER-CELL rational tables (per branching digit cell of each
outcome class o at each state τ), BEYOND the total cell-partition mass. Current: only
jP : ∀ e τ, T.Out e τ → PolyGeom + aggregate j_interp. Repair (additive; find the right
home — the structure carrying jP): add typed per-cell fields
    jPCell : ∀ e (τ : T.State e) (o : T.Out e τ), (the cell index type for o) → PolyGeom
    jcell_interp : per-cell interpolation law tying evalAt q₀ of (jPCell …).val to the
      per-cell measured value (the cell-fiber count/mass carrier — find the measured
      side's per-cell carrier; the auditor named M.Cell e τ — verify what exists in
      MeasuredSide and use it; if NO per-cell measured carrier exists, ADD the carrier
      field itself (a function field on MeasuredSide extensions is NOT allowed — instead
      put both the carrier and the law in a NEW structure JRatCells extending nothing,
      consumed as a typed premise where jP's aggregate is consumed), and
    jcell_sum : the aggregation equation — the sum of the per-cell presentations'
      values equals the aggregate rowVal/jP value at every pool.
Proofs/tables stay owner [1v]: fields are carried as data/hypotheses, NOT proved here.
The vacuity doctrine applies: each field's TYPE must pin its content (no bare Prop).

## S4 (wsh17_pin : Prop is a vacuous tag) — ACCEPTED
RS4Chain.wsh17_pin : Prop, consumed as h17 : C.wsh17_pin, UNUSED in rs4_rational_step —
degenerate (True works). Repair: read the note's CL-17 duty (ii) display (grep CL-17 in
§S-RESUM and the CL ledger; the auditor quotes: "every W_Ŝ is PRODUCED by the stated
rational machinery … remains OPEN here"). Then:
(a) Define def W17ii (…) : Prop with the statable core in RS4Chain's OWN vocabulary —
    at minimum a production law tying WshP/WshVal to the shallow carriers (shDom,
    shWeightH, visH, the height sum): e.g. ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools,
    WshVal Ŝ q₀ = tsum/∑ over shDom-visible heights of shWeightH — MATCH THE NOTE, do
    not invent; whatever needs §V-TABLES vocabulary stays out with the residue recorded
    in the docstring as the MovesV seam (wave 4).
(b) Change the FIELD TYPE: wsh17_pin : Prop becomes wsh17_pin : W17ii … (this is a
    definition change under the standing authority — it STRENGTHENS the interface to the
    note's content; document in the docstring: R57 + ratification finding 4). Wait —
    keep the field NAME. All instances must supply it: the n2 device has n2Wsh17Device
    (substantive per the auditor) — wire it to discharge the new type at n = 2; if it
    cannot, gate the n2 instance field with the honest sorry-free route (a hypothesis
    parameter on the device, reported).
(c) rs4_rational_step: if its conclusion genuinely does not consume CL-17(ii), REMOVE the
    unused h17 premise? NO — do not change its signature; instead ensure the theorem
    that DOES own the checksum's (ii)-conditionality consumes it; investigate which unit
    states the checksum conditional on CL-17(ii) per the note and report if the premise
    is misplaced (report only — no statement surgery beyond the field retyping).

## S5 (PolyGeom count semantics untyped) — ACCEPTED (typed value laws)
Note (CL-6/(iv)-POLY): T is ONE polynomial and each cell size ONE polynomial, each "valued
correctly at every prime power". Current PolyGeom: countT/countS arbitrary; only the
product is interpolated (tg_interp) — counts can be absorbed into geom. Repair: add a
typed value-law structure (additive; do NOT change PolyGeom itself — its uses are wide):
    structure PolyGeomLaws (…) : Prop-record tying, at every q₀ ∈ M.Pools (prime powers),
      evalAt q₀ countT = (the T-table count carrier at q₀) and
      evalAt q₀ countS = (the cell/state count carrier at q₀)
— find the measured count carriers in MeasuredSide (the auditor implies they exist for
the row: rowVal; per-table/per-cell counts may be MovesV seam material — same rule as S3:
type what is statable, record the seam residue in the docstring, NO bare Props). Consume:
add the laws as a typed premise to the (iv)-POLY-facing theorem(s) (identify: tg_interp's
consumers / the CL-6 unit) — as ADDITIONAL hypotheses-carrying VARIANTS (new theorem
names), leaving existing statements untouched.

## Deliverables (final response, ≤4000 tokens)
Per finding: what landed (file:decl), the note lines cited, build status, axiom check,
deviations with reasons, and the exact list of interface deltas (for the W4-SYNC record —
the wave-4 blueprints cite RS4Chain and will need the sync note). NO commits.
