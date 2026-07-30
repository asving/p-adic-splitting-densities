/-  TV-I2 (BRIDGE BP3, cluster c5; E-phase skeleton) — [FENCE, Q7 RULED:
    "extend toy if cheap, else census-backed record"] the `toyStrongPin`
    strengthening (GOLF_CAMPAIGN_2026-07-30.md A25 / SIGN-OFF QUEUE entry
    MovesSp#40): replace the CONSTANT/degenerate strong-verdict witness with
    one carrying DISCRIMINATING content — (c2) exactly-one across DISTINCT
    verdicts, (c3-b) REAL cap sensitivity.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.H (I2) + §4 (TV-I2).
    deps: none (SP8's built toy machinery only).

    CENSUS KERNEL, DECIDED AT TYPING TIME (the unit's first duty, done here):
    `toyCanModel.Branch := PUnit` — the model has EXACTLY ONE branch
    (`toyCanModel_branch_subsingleton` below, PROVED by structure eta), with
    the single closing-read datum `wordLast` and the constant verdict `.ep`.
    Therefore toyCanModel's OWN branches can NEVER discriminate ("two
    branches carry distinct Species data at their closing reads" is
    unsatisfiable at a subsingleton branch type), and the Q7 ruling's first
    arm fires: EXTEND THE TOY IF CHEAP — a second branch with distinct
    Species data at its closing read.  The sorried carriers below type that
    extension; if the prover finds no cheap second branch in the built
    catalogue vocabulary (G1 toy tables + the SP0/SP3 species machinery),
    the unit returns the census-backed "non-discriminating model" record
    against these statements instead (blocked-record, never fake
    discrimination — the blueprint's own exit).

    RESOLUTIONS (recorded):
    (1) FILE PLACEMENT: the cluster's files are prescribed under MovesV/;
      the declarations live in namespace LeanUrat.MovesV with the MovesSp
      vocabulary opened (no cycle: SP8 does not import MovesV units).
    (2) ADDITIVE ONLY: `toyStrongPin` (SP8_instantiation.lean:364) is NOT
      edited; the strengthened witness is a NEW model + pin pair.  The
      residual fold-in (re-pointing SP8's disclosure docstring / MANIFEST
      MovesSp#40 close-out at the strengthened witness) is an EDIT to
      existing files — orchestrator/prover-phase duty, reported, not done
      here.
    (3) "cap sensitivity" is typed as: the verdict map genuinely reads the
      word datum — verdicts are NOT determined by length alone
      (`toyStrongPinD_cap_sensitive`); with `hcap` this forces any two
      equal-length discriminated branches to differ at some read BELOW the
      cap, i.e. `hcap`'s premise is exercised (the constant witness made it
      vacuous for ANY cap, including 0 — the A25 disclosure).
    (4) "dict injective on them" is typed ON THE EMITTED VALUES (the tauV
      images of closing-read data), not on all of Vd (full-range injectivity
      Vd → Verdict is false on cardinality grounds and is NOT the queue's
      demand). -/
import LeanUrat.MovesSp.SP8_instantiation

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

open LeanUrat.MovesSp

/-- TV-I2 census kernel (PROVED): the built witness `toyCanModel` has a
SUBSINGLETON branch type (Branch := PUnit) — so the un-extended model cannot
carry two branches with distinct closing-read data, and the Q7
extend-if-cheap arm is the operative one. -/
theorem toyCanModel_branch_subsingleton (η η' : toyCanModel.Branch) :
    η = η' := rfl

/-- TV-I2 carrier: the EXTENDED toy model — a `CanTreeModel` at the same
(n, p, f) = (2, 2, f₂) key with (at least) TWO branches whose closing reads
carry DISTINCT Species data (the cheap-extension candidate: branch 0 = the
transported G1 toy A word ⟨wordHead, wordMid, wordLast⟩ as in `toyCanModel`;
branch 1 = a second catalogue word with a different closing read).  Every law
field discharged by computation on actual letters, as in `toyCanModel`. -/
noncomputable def toyCanModelD : CanTreeModel 2 2 f₂ := by
  sorry

/-- TV-I2 the DISCRIMINATING strong pin at the extended model: tauV reads
its Species argument (branch-reading, emitting {(1,1)} vs a second built
verdict), dict injective on the emitted values, cap := the closing-read
bound with `hcap` a REAL proof (agreement below cap covers the closing read
⇒ equal verdicts), htau by per-branch case analysis. -/
noncomputable def toyStrongPinD : StrongVerdictPin toyCanModelD := by
  sorry

/-- TV-I2 (c2) ACROSS DISTINCT VERDICTS: the extended model realizes two
branches with DIFFERENT verdicts — the exactly-one clause is exercised
across distinct values, not at a constant (the A25 disclosure's first gap). -/
theorem toyCanModelD_discriminates :
    ∃ η η' : toyCanModelD.Branch,
      toyCanModelD.verdict η ≠ toyCanModelD.verdict η' := by
  sorry

/-- TV-I2 tauV discrimination: the halting rule genuinely reads its Species
argument (the constant witness ignored it). -/
theorem toyStrongPinD_tau_discriminates :
    ∃ s s' : Species, toyStrongPinD.tauV s ≠ toyStrongPinD.tauV s' := by
  sorry

/-- TV-I2 dict injectivity ON THE EMITTED VALUES (resolution (4)): distinct
emitted tauV values at closing reads stay distinct through the bare-label
dictionary. -/
theorem toyStrongPinD_dict_inj_on_emitted :
    ∀ (η η' : toyCanModelD.Branch) (r r' : ℕ),
      toyCanModelD.len η = ((r + 1 : ℕ) : ℕ∞) →
      toyCanModelD.len η' = ((r' + 1 : ℕ) : ℕ∞) →
      toyStrongPinD.dict (toyStrongPinD.tauV (toyCanModelD.datum η r))
        = toyStrongPinD.dict (toyStrongPinD.tauV (toyCanModelD.datum η' r')) →
      toyStrongPinD.tauV (toyCanModelD.datum η r)
        = toyStrongPinD.tauV (toyCanModelD.datum η' r') := by
  sorry

/-- TV-I2 (c3-b) REAL cap sensitivity (resolution (3)): verdicts are NOT
determined by branch length alone — the verdict map reads the word datum,
so `hcap`'s cap-truncated-agreement premise is load-bearing (at the constant
witness this statement is FALSE, certifying the strengthening is real). -/
theorem toyStrongPinD_cap_sensitive :
    ¬ ∀ (η η' : toyCanModelD.Branch),
      toyCanModelD.len η = toyCanModelD.len η' →
      toyCanModelD.verdict η = toyCanModelD.verdict η' := by
  sorry

end LeanUrat.MovesV
