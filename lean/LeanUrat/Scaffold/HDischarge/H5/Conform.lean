/-
HDISCHARGE_H5 Wave 5 — conformance (`Conform.lean`).
Units C1/C2/C3 (chartered declarations) land here per BP §4.1/§4.7; C4 is
E-phase-gated (gate adjudicated below: NOT CLEARED — BLOCKED/DATA). This file
was opened by unit C5's spec record (below); C1–C3 provers extend it with
their declarations.

════════════════════════════════════════════════════════════════════════════
UNIT C5 — n = 3 route-a SPEC (BLOCKED/DATA; NO Lean unit lands now)
BP §4.7 row C5 + §2.5; design = R11_REPAIR_DESIGN_V5_2026-08-04.md §3.3.
════════════════════════════════════════════════════════════════════════════

STATUS at recording: BLOCKED/DATA — no n = 3 Lean-side tables exist in the
corpus (grep audit: `MovesS/` carries the N2* family only; no `BnMember 3`
instance, no N3 table anywhere under `LeanUrat/`). RESUM-n3 is a Python
numerics record only (`verification/CASE_RESUMN3_SEALED_PREDICTIONS.md`:
65/65 sealed integers exact — classifier-decided counts at every (σ, N),
p = 2 all N = 1..8, p = 3 all N = 1..5). This unit becomes EXECUTABLE only
when n = 3 tables land in Lean; until then it is a spec, not a theorem.

THE SPEC (design §3.3 (route-a), verbatim):

  "(route-a), n = 3: the OL-O12-2 transcription-and-correspondence pass
   (D-11 §5 clause 4's data half), EXTENDED BY ONE NAMED DUTY — per sealed
   row, verify the block's booking against the (O3) forms and the row
   against §2.3(iv)'s canonical assembly + the displayed (O3) scaling.
   (Finite data comparison; naming the duty prevents the pass from silently
   skipping the booking-profile half.)"

Unpacked as the pass's duty list, to be executed AT the landed n = 3 tables:
 (a) TRANSCRIPTION — land the complete degree-3 table as an (O3) member of
     𝔅₃ (`T3 : BnMember 3` + its roster), transcribed from OL-O12-2 (the
     D-11 §5 clause-4 data half; MATH_COMPLETION_TREE_2026-08-01 §OL-O12-2).
 (b) CORRESPONDENCE — instantiate `packOfMember`-side `PackCorrespondence`
     at T3 against the honest reference (`refOfMember T3 …`), by
     `decide`/`rfl` on the finite table (the C4 pattern at n = 3; no F1
     fence arises — there is no n = 3 device chain to fence).
 (c) PER-ROW BOOKING-PROFILE DUTY (the NAMED extension — never skipped):
     for EACH sealed block of T3, verify its booking against the (O3)
     forms; for EACH row, verify equality with §2.3(iv)'s canonical
     0/1-coefficient assembly + the displayed (O3) scaling (the
     `displayedRow` (O3) branch, unit D1). Machine face: produce
     `REWitness T3` by finite check — `booking ≠ Booking.O2`,
     `row_eq_displayed` at the (O3) form, `row_mem_entries`,
     `trow_canonical` — NOT via `mkREMember` (route-a verifies CONSUMED
     data; route-b constructs).
RETIREMENT on completion: (PACK-iv) + clause 4 retire AT THIS INSTANCE
(BP §1 door table); (g-i)–(g-iv) then convert the verified re-entrant
profile into the canonical row-form clause BY the §2.3(iv) definition.
Numeric precursor on record: RESUM-n3 65/65 (above). Blocking dependency:
the n = 3 tables themselves (owner: OL-O12-2/O-14d data campaign, not H5).
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H5.Defs
import LeanUrat.Scaffold.ValueSide.Hyps

namespace LeanUrat.Scaffold.HDischarge.H5

-- Unit C5 intentionally declares nothing: BLOCKED/DATA (see spec above).

end LeanUrat.Scaffold.HDischarge.H5

/-!
════════════════════════════════════════════════════════════════════════════
UNIT C1 — route-b conformance scaffolding (`packOfMember`/`refOfMember`/
`packOfMember_corr`). Statements VERBATIM from BP §4.7 row C1 (probed
skeleton); deps W0 + `Scaffold.ValueSide.Hyps`.
════════════════════════════════════════════════════════════════════════════

**MANDATORY caveats (BP §2.1 route-b, REVISION 2 — Codex gap 9), DISPLAYED:**

* (i) **SELF-conformance, NOT clause-4 law-transfer.** `packOfMember_corr` is
  scaffolding for the route: BOTH sides of the `PackCorrespondence` read the
  SAME member `T` (`refOfMember` reads the identical Σ-type data; the
  `UCarriers` argument `C` is the reference's phantom key, consumed by the
  TYPE only). The transfer claim needs the row-identity seam — C3's
  `ref_reads_member` at the entry level now; the σ-keyed row pin is F2/route
  territory. What remains OPEN is the identification of the REALIZED corpus
  tables (the classifier-built pack Steps 17/18 actually consume) with
  `packOfMember` of the intended member: exactly OL-O12-2's data half / the
  O-14d population duty (route-a at n = 3, spec above; O-14d at general n).
  NO claim of it is made here.
* (ii) **Finset `Row` collapses equal entries.** The Σ-type over `Finset Qq`
  identifies distinct table rows carrying equal rational-function entries —
  "entry-for-entry" at the source is a statement about TABLE POSITIONS; a
  multiset/position-indexed `Row` refinement is the E-phase option if the
  O-14d population needs position fidelity.
* **Landing decision (C1 prover, recorded at landing per BP §2.1):** the
  Finset Σ-type `Row` is KEPT exactly as probed; the position-indexed
  refinement is NOT taken now (no landed consumer reads position
  multiplicity), and it stays on record as the displayed E-phase option (ii).
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType)
open LeanUrat.MovesS (OKat evalAt powSubst)

-- `T` in `packOfMember` (the member key, BP-mandated binder) and `C` in
-- `refOfMember` (the phantom `UCarriers` key) are deliberately unread —
-- exactly caveat (i). Silence the linter for these two BP-verbatim binders.
set_option linter.unusedVariables false

/-- **[HDISCHARGE_H5 unit C1]** The route-b assembled pack READ OFF a member:
the Σ-type table over the roster `rowsOf` (at call sites `rowsOf := T.entries`),
with `Row = (e : Finset.Icc 1 n) × {g : Qq // g ∈ rowsOf e.1}`,
`entry r = r.2.1`, `blockOf r = r.1.1`; the Fintype instance is the
`Sigma.instFintype` route. The member argument `T` keys the pack to the member
(the call-site discipline). Caveat (ii) of the C1 header block applies: this
`Row` collapses positionally distinct rows with equal entries. -/
noncomputable def packOfMember {n : ℕ} (T : BnMember n)
    (rowsOf : ℕ → Finset Qq) : ValueSide.AssembledPack n where
  Row := (e : Finset.Icc 1 n) × {g : Qq // g ∈ rowsOf e.1}
  instR := Sigma.instFintype
  entry r := r.2.1
  blockOf r := r.1.1
  blockOf_pos r := (Finset.mem_Icc.mp r.1.2).1
  blockOf_le r := (Finset.mem_Icc.mp r.1.2).2

/-- **[HDISCHARGE_H5 unit C1]** The reference reading the SAME member data into
`PackReference n C (packOfMember T rowsOf)`: `intendedEntry`/`intendedBlock`
are the identical Σ-type reads. `C` is the phantom `UCarriers` key demanded by
the `PackReference` TYPE — nothing here reads it (caveat (i) of the C1 header
block: self-conformance scaffolding, not the clause-4 law-transfer). -/
noncomputable def refOfMember {n : ℕ} (C : MovesU.UCarriers n)
    (T : BnMember n) (rowsOf : ℕ → Finset Qq) :
    ValueSide.PackReference n C (packOfMember T rowsOf) where
  intendedEntry r := r.2.1
  intendedBlock r := r.1.1
  intendedBlock_pos r := (Finset.mem_Icc.mp r.1.2).1
  intendedBlock_le r := (Finset.mem_Icc.mp r.1.2).2

/-- **[HDISCHARGE_H5 unit C1]** Route-b SELF-conformance: `packOfMember` at
`rowsOf := T.entries` corresponds `rfl`-field-wise to `refOfMember` reading the
same member. MANDATORY C1-header caveats (i)/(ii) apply IN FULL: this is
scaffolding for route-b, NOT the clause-4 law-transfer, and the Finset `Row`
is position-collapsing. -/
theorem packOfMember_corr {n : ℕ} (C : MovesU.UCarriers n) (T : BnMember n) :
    ValueSide.PackCorrespondence n C (packOfMember T T.entries)
      (refOfMember C T T.entries) where
  entry_eq _ := rfl
  block_eq _ := rfl

end LeanUrat.Scaffold.HDischarge.H5

/-!
════════════════════════════════════════════════════════════════════════════
UNIT C4 — n = 2 instance gate: GATE ADJUDICATION (E-phase; recorded
2026-08-01, prover C4). BP §4.7 row C4 + §2.1 route-a paragraph.
════════════════════════════════════════════════════════════════════════════

**CARRIER-CHOICE ADJUDICATION against the M04 F1 fence** (the required gate
paragraph; fence source: `lean/notes/openmath/M04-series-tie_fable.md` §0 +
§4 Proposition F1, restated as a standing fence at `blueprints/BP_IV.md`
§1.5). The DEVICE n = 2 chain (`n2Chain`, `MovesS/N2Sigmas.lean`, over the
N2* carriers `n2T`/`n2M`/`n2RB`) is FENCED from value claims: its Rval
triple (split q²/(q²+q+1), inert (q+1)/(q²+q+1), ram 0) carries a zero
entry and two distinct entries, while the project-validated true monic
quadratic ℤ_p densities are (p/(2(p+1)), p/(2(p+1)), 1/(p+1)) — two equal
positive entries, no zero (M04 numeric certificate, exact rationals at
p ∈ {2,3,5,7}; no bijective verdict re-assignment repairs it). C4's charter
is the n = 2 INSTANCE gate for the (PACK) row — an inhabitant of the very
`PackCorrespondence` binder (`hpack`) S5 consumes — so instantiating it at
device-derived data would manufacture an S5-consumable n = 2 witness
carrying no ℤ_p content: exactly what the fence forbids ("the DEVICE n = 2
chain must never instantiate S5's carriers; only the S-area's real pack
qualifies"). RULING: carrier REJECTED — anything read off the device chain;
carrier REQUIRED — `packOfMember T2 T2.entries` at an S-area REAL-pack
member `T2 : BnMember 2` (the value-correct n = 2 tables, whose Rval
carries the true densities), against `refOfMember C T2 T2.entries` reading
the same member; the C1-header caveat (i) stays displayed even then (the
correspondence is route-b self-conformance; the clause-4 content is the
realized-tables ↔ T2 identification, a finite data pass at the honest
member).

**GATE OUTCOME: NOT CLEARED — BLOCKED/DATA (the C5 class).** Unit C1
(`packOfMember`/`refOfMember`/`packOfMember_corr`, above) landed this wave,
so the SOLE remaining blocker is data: no `T2 : BnMember 2` exists at HEAD
(grep audit 2026-08-01: the only concrete n = 2 chain-side instances under
`LeanUrat/` are the device `n2Chain` and the adversarial negative
`UCarriers 2` witnesses of `MovesU/BridgeRosterPins.lean` /
`MovesU/BridgeB15a_r2Neg.lean` — all fenced or countermodel). The honest
reference exists as NUMERICS only (BP §2.1 "the real-pack numerics";
`verification/padic_types.py`, oracle-validated). Landing T2 = the
value-correct symbolic n = 2 member (M04 Theorem 4 open kernel K3
territory) + the route-a verification pass — owner: the OL-O12-2/O-14d
data campaign, NOT an H5 unit; manufacturing T2 here would smuggle the
value-correctness claim. Per the E-PHASE GATE ("do NOT run a prover before
the gate clears"), no prover ran; unit C4 declares NOTHING at HEAD.
EXECUTABLE FORM once T2 lands: `packOfMember_corr C T2` (rfl-fields) +
`decide`/`rfl` on T2's finite roster — the pattern unit C5's duty (b)
cites at n = 3, WITH the F1 carrier ruling above binding the n = 2 choice.
-/

namespace LeanUrat.Scaffold.HDischarge.H5

-- Unit C4 intentionally declares nothing at HEAD: gate adjudicated
-- NOT CLEARED — BLOCKED/DATA (see the C4 adjudication block above).

end LeanUrat.Scaffold.HDischarge.H5

/-!
════════════════════════════════════════════════════════════════════════════
UNIT C3 — the `H5PackTyped` bundle + consumption theorem `h5PackTyped_laws`.
Statement per BP §4.7 row C3 (REVISION 2, folding Codex critical 5;
RE-PROBED at the §4.0 r2 round); deps W0, parallel with C1.
════════════════════════════════════════════════════════════════════════════

The bundle rides the ACTUAL witnesses `(T : BnMember n) (W : REWitness T)
(M : MassFacts T W)` — not `Nonempty` (the r1 form): B2's consumption needs
the witnesses themselves.

**DEDUP/OWNERSHIP (BP §4.7 C3, folding Codex gap 12), DISPLAYED:** the bundle
duplicates NO law — every field is a NAMED earlier unit's conclusion shape:
* `corr` — the landed BP_IV H2b carrier `ValueSide.PackCorrespondence`
  (consumed, never redefined);
* `ref_reads_member` — the T↔R ENTRY-LEVEL tie the r1 form lacked; the
  σ-keyed identification of realized table rows stays route-a/route-b
  territory (BP §2.1 — DISPLAYED, never claimed here);
* `wsh` — unit K2a's conclusion shape (`bnMember_entries_mem_OKat`);
* `bdd` — unit B2's conclusion shape (`beta_eval_mem_Icc`), `e ≤ n`-scoped;
* `solve_interp` — unit P1's conclusion shape (`beta_eval_solve`, the
  (PACK-i) BLOCK form; the K2 chain-vocabulary form `RS4Chain.rsh_interp`
  rides the chain-instance seam, BP §2.2 — never claimed here).

`H5PackTyped` is chartered as THE FIELD-REFINEMENT TARGET for BP_VI's
`h5_pack` (a bare Prop at ROOT-REVISION-5 sync, `Scaffold/Hypotheses.lean`):
at refinement time BP_VI lands the equivalence/migration theorem and owns
the swap — H5 never edits `Hypotheses.lean` (BP §6 item 6). No discharge of
(H5) at ROOT is claimed here: the bundle is a consumption CARRIER; its law
fields are populated at members by the earlier H5 units, and clause 4 /
(PACK-iv) at the consumed instance stay open (BP §6 items 1–2).
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType)
open LeanUrat.MovesS (OKat evalAt powSubst)

/-- **[HDISCHARGE_H5 unit C3]** The typed (H5)/(PACK) bundle at a member
carrying the ACTUAL witnesses `(T, W, M)` (`W`/`M` ride as parameters so a
consumer can fire B1/B2 at the same member — the r1 `Nonempty` form was too
weak). FIVE fields, each a NAMED earlier unit's conclusion shape (header
block above); no law is duplicated and none is discharged here. -/
structure H5PackTyped {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) (C : MovesU.UCarriers n)
    (P : ValueSide.AssembledPack n)
    (R : ValueSide.PackReference n C P) : Prop where
  /-- Clause 4's correspondence at the landed BP_IV H2b carrier: the
  assembled pack reads entry-for-entry as the intended reference. -/
  corr : ValueSide.PackCorrespondence n C P R
  /-- The T↔R ENTRY-LEVEL tie (REVISION 2, Codex critical 5): every intended
  entry is a member entry at its intended block. The σ-keyed identification
  stays route territory (BP §2.1) — never claimed here. -/
  ref_reads_member : ∀ r : P.Row,
    R.intendedEntry r ∈ T.entries (R.intendedBlock r)
  /-- (PACK-iii) at the member's entry roster — unit K2a's conclusion shape
  (`bnMember_entries_mem_OKat`). -/
  wsh : ∀ e, ∀ g ∈ T.entries e, ∀ q₀ : ℚ, 2 ≤ q₀ → g ∈ OKat q₀
  /-- (PACK-ii) at the member — unit B2's conclusion shape
  (`beta_eval_mem_Icc`), `e ≤ n`-scoped. -/
  bdd : ∀ q₀ : ℚ, 2 ≤ q₀ → ∀ e : ℕ, e ≤ n → ∀ σ : SplittingType n,
    ∀ h : T.β e σ ∈ OKat q₀, evalAt q₀ ⟨T.β e σ, h⟩ ∈ Set.Icc (0 : ℚ) 1
  /-- (PACK-i) BLOCK form at the member — unit P1's conclusion shape
  (`beta_eval_solve`): the solve β = u⁻¹·t commutes with `evalAt`. -/
  solve_interp : ∀ (e : ℕ) (he : 2 ≤ e) (q₀ : ℚ), 2 ≤ q₀ →
    ∀ (σ : SplittingType n) (hβ : T.β e σ ∈ OKat q₀)
      (ht : (T.blocks e he).trow σ ∈ OKat q₀)
      (hu : (T.blocks e he).u ∈ OKat q₀),
      evalAt q₀ ⟨(T.blocks e he).u, hu⟩ ≠ 0 →
      evalAt q₀ ⟨T.β e σ, hβ⟩
        = (evalAt q₀ ⟨(T.blocks e he).u, hu⟩)⁻¹
          * evalAt q₀ ⟨(T.blocks e he).trow σ, ht⟩

/-- **[HDISCHARGE_H5 unit C3]** Consumption theorem: one bundle hypothesis
unpacks to the five member conclusions (the BP_VI `h5_pack` consumption seam —
a downstream consumer binds `H5PackTyped` once and reads the laws off this
conjunction). PURE unpacking: each conjunct is the corresponding field's
exact shape; no derivation is smuggled. -/
theorem h5PackTyped_laws {n : ℕ} {T : BnMember n} {W : REWitness T}
    {M : MassFacts T W} {C : MovesU.UCarriers n}
    {P : ValueSide.AssembledPack n} {R : ValueSide.PackReference n C P}
    (hP : H5PackTyped T W M C P R) :
    ValueSide.PackCorrespondence n C P R ∧
    (∀ r : P.Row, R.intendedEntry r ∈ T.entries (R.intendedBlock r)) ∧
    (∀ e, ∀ g ∈ T.entries e, ∀ q₀ : ℚ, 2 ≤ q₀ → g ∈ OKat q₀) ∧
    (∀ q₀ : ℚ, 2 ≤ q₀ → ∀ e : ℕ, e ≤ n → ∀ σ : SplittingType n,
      ∀ h : T.β e σ ∈ OKat q₀,
        evalAt q₀ ⟨T.β e σ, h⟩ ∈ Set.Icc (0 : ℚ) 1) ∧
    (∀ (e : ℕ) (he : 2 ≤ e) (q₀ : ℚ), 2 ≤ q₀ →
      ∀ (σ : SplittingType n) (hβ : T.β e σ ∈ OKat q₀)
        (ht : (T.blocks e he).trow σ ∈ OKat q₀)
        (hu : (T.blocks e he).u ∈ OKat q₀),
        evalAt q₀ ⟨(T.blocks e he).u, hu⟩ ≠ 0 →
        evalAt q₀ ⟨T.β e σ, hβ⟩
          = (evalAt q₀ ⟨(T.blocks e he).u, hu⟩)⁻¹
            * evalAt q₀ ⟨(T.blocks e he).trow σ, ht⟩) :=
  ⟨hP.corr, hP.ref_reads_member, hP.wsh, fun _ hq _ he σ h => hP.bdd _ hq _ he σ h,
    hP.solve_interp⟩

end LeanUrat.Scaffold.HDischarge.H5

/-!
════════════════════════════════════════════════════════════════════════════
UNIT C2 — `mkREMember`, the route-b builder. BP §4.7 row C2 + §2.5 Builder
paragraph (REVISION 2 duty list per Codex critical 2); deps W0 (`Defs.lean`).
════════════════════════════════════════════════════════════════════════════

From `(C : BnCoordinates n)` re-entrant-booked + per-block `ExitData` + the
solve data, produce `(T : BnMember n) × REWitness T` where the builder
* DEFINES `row e σ := displayedRow C.system.booking e β (E e) σ`,
* puts the constructed rows INTO the built member's `entries` roster (a
  builder duty, not an assumption), so
* `trow_canonical` / `row_eq_displayed` are `rfl`-class (recorded as the
  external `rfl` theorems `mkREMember_trow` / `mkREMember_row` below), and
* `row_mem_entries` is discharged BY CONSTRUCTION, never assumed.

What "by construction" honestly covers (BP §2.5): the (RE) OPERATIVE content
per the (δ4) adjudication at the CONSTRUCTED member — design §3.3 (route-b)'s
"the profile then holds BY CONSTRUCTION and is checkable at population time".
The identification of any CONSUMED member with the constructed one stays
clause-4/route territory (BP §2.1) — never claimed here.

**Roster-compilation choice, DISPLAYED (trust surface for the Codex pass):**
`BnCoordinates.Valid.entries_eq` pins the entries roster to the three §2.3
families (weights ∪ divisor-pattern masses ∪ polygon masses), so the ONLY
`Valid`-compatible way to put the constructed rows into the roster is through
one of the three families. The builder inserts them into the WEIGHTS slot
(`reWeights`), whose membership condition is exactly `Gram` — and under the
solve data every displayed row is a VALUE of ℛ_cyc = ℚ[q][𝒮⁻¹]
(`GramOver.memRcyc` over the solved legs), hence leaflessly 𝒢-generated as
s⁻¹·P (`gram_of_memRcyc`, the converse bridge to the landed `Gram.memRcyc`).
HONESTY RESIDUE: "weights" is §2.3's family (v) semantically; counting the
constructed family-(iv) rows in the weights SLOT is a roster-compilation
choice at the corpus granularity (the roster is an un-indexed `Finset`, the
BP §2.5 granularity residue) — displayed here, not smuggled.

Route reuse (per the C2 row): `gramOver_rowOf` (landed II-R8) walks each
verdict row, `GramOver.finsetSum` (landed II-R3) aggregates the exit strata;
the (O2′) leg rides the landed `gram_kappa1`, the (O3) leg the landed
`gramOver_o3scale`; the solve denominators are `solveU_unit`.
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType Gram)
open LeanUrat.MovesS (OKat evalAt powSubst)

open scoped Classical

/-- ℛ_cyc-membership implies leafless 𝒢-generation: `f = s⁻¹·P` with `s ∈ 𝒮`
is the `(g2)·(g1)` composite `(invS hs).mul (poly P)`. Converse bridge to the
landed `Gram.memRcyc`; C2's device for putting ℛ_cyc-valued rows into a
`Valid` weights roster. [HDISCHARGE_H5 unit C2 helper] -/
theorem gram_of_memRcyc {f : Qq} (hf : MemRcyc f) : Gram f := by
  obtain ⟨P, s, hs, hP⟩ := hf
  have hsne : algebraMap (Polynomial ℚ) Qq s ≠ 0 :=
    RatFunc.algebraMap_ne_zero (MovesU.cycS_ne_zero hs)
  have hf' : f = (algebraMap (Polynomial ℚ) Qq s)⁻¹
      * algebraMap (Polynomial ℚ) Qq P := by
    rw [← hP, ← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
  rw [hf']
  exact (Gram.invS hs).mul (Gram.poly P)

/-- The canonical aggregate `tRow` is 𝒢-generated over the lower legs:
`GramOver.finsetSum` (landed II-R3) over the per-stratum `gramOver_rowOf`
(landed II-R8) walks. [HDISCHARGE_H5 unit C2 helper] -/
theorem gramOver_tRow {n : ℕ} {β : ℕ → SplittingType n → Qq} {e : ℕ}
    (E : ExitData n) (hm : ∀ F : E.idx, Gram (E.mass F))
    (hH : ∀ F : E.idx, ∀ x ∈ E.handoff F, x.1 < e) (σ : SplittingType n) :
    GramOver (lowerLegs β e) (tRow β E σ) := by
  show GramOver (lowerLegs β e)
    (∑ F : E.idx, rowOf β (E.mass F) (E.handoff F) (E.comp F) σ)
  exact GramOver.finsetSum _ _ fun F _ => gramOver_rowOf (hm F) _ (hH F) _ σ

/-- Every displayed row (any booking) is 𝒢-generated over the legs at depth
≤ e: the aggregate by `gramOver_tRow` (lower legs, monotoned up), the (O2′)
adjustment by the landed `gram_kappa1` times the `leaf` β_e(σ) (depth exactly
e — hence the `≤ e` set), the (O3) scaling by the landed `gramOver_o3scale`.
The `Booking.O2` branch is the guarded placeholder (= the unadjusted t):
provable, never consumed under (RE). [HDISCHARGE_H5 unit C2 helper] -/
theorem gramOver_displayedRow {n : ℕ} {β : ℕ → SplittingType n → Qq} {e : ℕ}
    (b : Booking) (E : ExitData n) (hm : ∀ F : E.idx, Gram (E.mass F))
    (hH : ∀ F : E.idx, ∀ x ∈ E.handoff F, x.1 < e) (σ : SplittingType n) :
    GramOver {f | ∃ e' ≤ e, ∃ σ', f = β e' σ'} (displayedRow b e β E σ) := by
  have hsub : lowerLegs β e ⊆ {f | ∃ e' ≤ e, ∃ σ', f = β e' σ'} := by
    rintro g ⟨e', he', σ', rfl⟩
    exact ⟨e', le_of_lt he', σ', rfl⟩
  have ht : GramOver {f | ∃ e' ≤ e, ∃ σ', f = β e' σ'} (tRow β E σ) :=
    GramOver.mono hsub (gramOver_tRow E hm hH σ)
  cases b with
  | O1 => exact ht
  | O2 => exact ht
  | O2r =>
    exact ht.add ((Gram.gramOver (gram_kappa1 e)).mul
      (GramOver.leaf ⟨e, le_rfl, σ, rfl⟩))
  | O3 => exact gramOver_o3scale ht

/-- The route-b block presentations: `trow := tRow β (E e)` (canonical, so
`REWitness.trow_canonical` is `rfl`-class), solve denominator
`u := booking.solveU e` with the landed `solveU_unit` (so `BnMember.hblockU`
is `rfl`-class too). [HDISCHARGE_H5 unit C2 component] -/
noncomputable def mkREBlocks {n : ℕ} (C : BnCoordinates n) (E : ℕ → ExitData n)
    (β : ℕ → SplittingType n → Qq)
    (hlt : ∀ e, ∀ F : (E e).idx, ∀ x ∈ (E e).handoff F, x.1 < e)
    (hmass : ∀ e, ∀ F : (E e).idx, Gram ((E e).mass F))
    (hsolve : ∀ e, 2 ≤ e → ∀ σ,
      β e σ = (C.system.booking.solveU e)⁻¹ * tRow β (E e) σ) :
    ∀ e, 2 ≤ e → BlockPresentation n β e := fun e he =>
  { trow   := tRow β (E e)
    htrow  := fun σ => gramOver_tRow (E e) (hmass e) (hlt e) σ
    u      := C.system.booking.solveU e
    hu     := solveU_unit C.system.booking he
    hsolve := hsolve e he }

/-- The route-b weights roster: the input weights PLUS the constructed
displayed rows at every block (the roster-compilation choice displayed in
the C2 header block). [HDISCHARGE_H5 unit C2 component] -/
noncomputable def reWeights {n : ℕ} (C : BnCoordinates n) (E : ℕ → ExitData n)
    (β : ℕ → SplittingType n → Qq) (e : ℕ) : Finset Qq :=
  C.weights e ∪
    Finset.image (fun σ => displayedRow C.system.booking e β (E e) σ)
      Finset.univ

/-- The route-b entries roster, in `Valid.entries_eq`'s exact three-family
shape over `reWeights` — so the built coordinates satisfy `entries_eq` by
`rfl` and the constructed rows are IN the roster by construction.
[HDISCHARGE_H5 unit C2 component] -/
noncomputable def reEntries {n : ℕ} (C : BnCoordinates n) (E : ℕ → ExitData n)
    (β : ℕ → SplittingType n → Qq) (e : ℕ) : Finset Qq :=
  reWeights C E β e ∪
    (C.pattData e).image (massPatt e) ∪
    (C.polygonData e).image (fun z => massPoly e z.1 z.2.1 z.2.2)

/-- **[HDISCHARGE_H5 unit C2] `mkREMember` — the route-b builder** (REVISION
2 duty list per Codex critical 2): from re-entrant-booked coordinates `C`
(with `C.Valid` for the INPUT roster), per-block `ExitData` (descending
hand-offs `hlt`, 𝒢 masses `hmass`), and the solve data (`β` with ℛ base
blocks `hbase` and the `solveU`-division solve identity `hsolve`), produce
the `BnMember` together with its `REWitness`:

* `row e σ := displayedRow C.system.booking e β (E e) σ` — DEFINED, so
  `row_eq_displayed` is `rfl`;
* the constructed rows go INTO the built `entries` roster (`reEntries`, via
  the `reWeights` slot) — so `row_mem_entries` is discharged by
  construction, NEVER assumed;
* `trow_canonical` is `rfl` (`mkREBlocks` sets `trow := tRow β (E e)`).

The (RE) profile at the CONSTRUCTED member holds by construction; the
identification with any CONSUMED member stays clause-4/route territory (BP
§2.1, §2.5 — the C2 header block above). -/
noncomputable def mkREMember {n : ℕ} (C : BnCoordinates n) (hC : C.Valid)
    (hbook : C.system.booking ≠ Booking.O2)
    (E : ℕ → ExitData n)
    (hlt : ∀ e, ∀ F : (E e).idx, ∀ x ∈ (E e).handoff F, x.1 < e)
    (hmass : ∀ e, ∀ F : (E e).idx, Gram ((E e).mass F))
    (β : ℕ → SplittingType n → Qq)
    (hbase : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ))
    (hsolve : ∀ e, 2 ≤ e → ∀ σ,
      β e σ = (C.system.booking.solveU e)⁻¹ * tRow β (E e) σ) :
    (T : BnMember n) × REWitness T :=
  ⟨{ coords := { C with weights := reWeights C E β, entries := reEntries C E β }
     valid :=
       { weight_gram := by
           intro e g hg
           rcases Finset.mem_union.mp hg with hw | hrow
           · exact hC.weight_gram e g hw
           · obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hrow
             refine gram_of_memRcyc (GramOver.memRcyc ?_
               (gramOver_displayedRow C.system.booking (E e) (hmass e) (hlt e) σ))
             rintro f ⟨e', -, σ', rfl⟩
             exact beta_memRcyc hbase (mkREBlocks C E β hlt hmass hsolve) e' σ'
         handoff_step := hC.handoff_step
         entries_eq := fun _ => rfl }
     β := β
     hbase := hbase
     blocks := mkREBlocks C E β hlt hmass hsolve
     hblockU := fun _ _ => rfl
     entries := reEntries C E β
     entries_eq := rfl
     hentries := by
       intro e g hg
       rcases Finset.mem_union.mp hg with hg' | hpoly
       · rcases Finset.mem_union.mp hg' with hg'' | hpatt
         · rcases Finset.mem_union.mp hg'' with hw | hrow
           · exact Gram.gramOver (hC.weight_gram e g hw)
           · obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hrow
             exact gramOver_displayedRow C.system.booking (E e) (hmass e) (hlt e) σ
         · obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hpatt
           exact Gram.gramOver (gram_massPatt e P)
       · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hpoly
         exact Gram.gramOver (gram_massPoly e z.1 z.2.1 z.2.2) },
   { exits := E
     handoff_lt := hlt
     booking_reentrant := hbook
     trow_canonical := fun _ _ => rfl
     row := fun e σ => displayedRow C.system.booking e β (E e) σ
     row_eq_displayed := fun _ _ _ _ => rfl
     row_mem_entries := fun _ σ _ _ =>
       Finset.mem_union_left _ (Finset.mem_union_left _
         (Finset.mem_union_right _
           (Finset.mem_image_of_mem _ (Finset.mem_univ σ)))) }⟩

/-- `rfl`-class record (BP §4.7 C2 duty): the built witness's `row` IS the
displayed row, definitionally. -/
theorem mkREMember_row {n : ℕ} (C : BnCoordinates n) (hC : C.Valid)
    (hbook : C.system.booking ≠ Booking.O2)
    (E : ℕ → ExitData n)
    (hlt : ∀ e, ∀ F : (E e).idx, ∀ x ∈ (E e).handoff F, x.1 < e)
    (hmass : ∀ e, ∀ F : (E e).idx, Gram ((E e).mass F))
    (β : ℕ → SplittingType n → Qq)
    (hbase : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ))
    (hsolve : ∀ e, 2 ≤ e → ∀ σ,
      β e σ = (C.system.booking.solveU e)⁻¹ * tRow β (E e) σ)
    (e : ℕ) (σ : SplittingType n) :
    (mkREMember C hC hbook E hlt hmass β hbase hsolve).2.row e σ
      = displayedRow C.system.booking e β (E e) σ := rfl

/-- `rfl`-class record (BP §4.7 C2 duty): the built member's block aggregate
IS the canonical `tRow`, definitionally. -/
theorem mkREMember_trow {n : ℕ} (C : BnCoordinates n) (hC : C.Valid)
    (hbook : C.system.booking ≠ Booking.O2)
    (E : ℕ → ExitData n)
    (hlt : ∀ e, ∀ F : (E e).idx, ∀ x ∈ (E e).handoff F, x.1 < e)
    (hmass : ∀ e, ∀ F : (E e).idx, Gram ((E e).mass F))
    (β : ℕ → SplittingType n → Qq)
    (hbase : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ))
    (hsolve : ∀ e, 2 ≤ e → ∀ σ,
      β e σ = (C.system.booking.solveU e)⁻¹ * tRow β (E e) σ)
    (e : ℕ) (he : 2 ≤ e) :
    ((mkREMember C hC hbook E hlt hmass β hbase hsolve).1.blocks e he).trow
      = tRow β (E e) := rfl

/-- `rfl`-class record: the built member solves with the INPUT solve data `β`
and carries the INPUT booking — the builder invents nothing. -/
theorem mkREMember_beta {n : ℕ} (C : BnCoordinates n) (hC : C.Valid)
    (hbook : C.system.booking ≠ Booking.O2)
    (E : ℕ → ExitData n)
    (hlt : ∀ e, ∀ F : (E e).idx, ∀ x ∈ (E e).handoff F, x.1 < e)
    (hmass : ∀ e, ∀ F : (E e).idx, Gram ((E e).mass F))
    (β : ℕ → SplittingType n → Qq)
    (hbase : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ))
    (hsolve : ∀ e, 2 ≤ e → ∀ σ,
      β e σ = (C.system.booking.solveU e)⁻¹ * tRow β (E e) σ) :
    (mkREMember C hC hbook E hlt hmass β hbase hsolve).1.β = β ∧
    (mkREMember C hC hbook E hlt hmass β hbase hsolve).1.booking
      = C.system.booking := ⟨rfl, rfl⟩

end LeanUrat.Scaffold.HDischarge.H5
