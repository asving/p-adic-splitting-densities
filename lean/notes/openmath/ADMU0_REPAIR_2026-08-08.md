# ADM-U0 triangular repair — verification record (2026-08-08, wallclock 2026-08-02)

**Unit:** ADM-U0 triangular repair (synthesis pass 5 F1 target (ii), queue #7:
"ADM-U0 triangular repair (known defect, authority on file) before ADM-U6a/U6b").

**VERDICT: ALREADY EXECUTED — the queue line is stale.** The repair landed at the
HDISCHARGE_H3 Wave 0 fleet, commit `e1cf117` (2026-08-01 15:06 UTC; content rode WIP
sweep `6ba826d`), one of the "seven parallel W0 units" the ledger's H3 FAN-OUT 12/18
entry records as landed. This unit re-verified the mandate, the landed diff, and the
compile chain at HEAD; **no edit was needed and none was made** (Lean tree untouched).

## Mandate leg (a) — the defect (HDISCHARGE_H3 §1.3(b), finding (F-ADM-1))

> "The `triangular` axiom degenerates ramified deep stages. `CensusData.triangular :
> ∀ i, i.1 ≠ 0 → e i ∣ h i` TOGETHER WITH `h_coprime : gcd(h i, e i) = 1` forces
> e_i = 1 at every stage i ≥ 1 (e_i ∣ h_i ∧ coprime ⟹ e_i = 1). Consequence: the
> as-built carrier CANNOT EXPRESS the K6 countermodel datum (e₁ = 3, h₁ = 2: 3 ∤ 2
> fails `triangular`) nor any ramified stage-≥1 type."

## Mandate leg (b) — the repair authority (HDISCHARGE_H3 §1.4, unit ADM-U0)

> "ADM-U0 [EDIT-GATED; definition-change authority; wave 0]. Adjudicate (F-ADM-1):
> drop `triangular` from `CensusData` (keep `he/hf/h_coprime`), OR record the
> deliberate e_{≥1} = 1 fence with a rename. Ripple: grep-audited (structure +
> `gateData` only); re-prove `gateData` fields; full `lake build` + AxChk."

Adjudication basis (recorded in the landed docstring): O-9 rev5 §1's pinned data
sheet has λ_i = −h_i/e_i in lowest terms — coprimality ONLY, e_i > 1 live at stages
≥ 1 (warning display 1) — so the row was a transcription defect of the BP_IV §1.2
display (the C1/C2 `ledgerE` precedent, REVISION 3). The DROP branch was taken.

## The landed diff (commit 6ba826d, `Scaffold/ValueSide/CensusCore.lean`)

- REMOVED the structure field: `triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i`
  (`he/hf/h_coprime` are now the complete axiom set on `CensusData`);
- ADDED the "ADM-U0 REPAIR RECORD" docstring on `CensusData` (defect, adjudication
  source, disposition);
- `Census.lean` (+90/−): the padding-clause SATISFIABILITY RECORD rewritten to
  RESOLVED (the three compiled degeneracy witnesses `e_eq_one_of_ne_zero` /
  `period_eq_one` / `attainDim_pos` retired with the row they witnessed against);
  `gateData` needed no `triangular` field post-drop.

## Verification performed at HEAD (this unit, 2026-08-02 wallclock)

1. `CensusData` at HEAD carries exactly `r/e/h/f/he/hf/h_coprime` — no `triangular`.
2. `grep -rn triangular` over `Scaffold/ValueSide/` + `Scaffold/HDischarge/`: every
   hit is repair-record documentation or the unrelated unitriangular/block-triangular
   vocabulary; the field is gone.
3. Downstream consumption live: `AdmGates.lean` K6 gate compiles the post-repair
   expressibility ("a RAMIFIED datum (e₁ = 2 > 1: expressible only post-ADM-U0)");
   `AdmCarrier.lean` cites the record for non-vacuity.
4. Compile chain re-checked: `lake env lean LeanUrat/Scaffold/HDischarge/H3/AdmGates.lean`
   (imports CensusCore → Census → AdmCarrier) — **exit 0, zero diagnostics**.
5. Zero `sorry` in `Scaffold/HDischarge/H3/` and `CensusCore.lean`; working tree
   clean in both directories.

## Disposition

The ADM-U6a/U6b blocker named by synthesis passes 4/5 is DISCHARGED (and was at
those passes' write time — the queue line carried forward from the pass-4 text,
which predates the wave-0 landing by hours). ADM-U6a/U6b remain gated on their OWN
gates per HDISCHARGE_H3 §1.4 (G-ADM-2 = hit, or track-A stall election; sign-off
gated), NOT on ADM-U0.
