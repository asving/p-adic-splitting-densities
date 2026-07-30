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

/-- TV-I2 second-branch letter 1 (the CHEAP EXTENSION, found in the catalogue
vocabulary): the read-1 species at STRIDE e = 2 — same stage (D, w, W) =
(1, 1, 2) as `wordMid` (StageLaws from `wordHead`'s selection (1, 2) force the
stage), but window composition 0 + 2·1 + 0 = 2 (e = 2, ℓ = 1, no flanks)
instead of `wordMid`'s 0 + 1·1 + 1.  λ = {(1, 1)} by (G4) Σgμ = ℓ = 1,
selection (1, 1). -/
def wordMidB : Species :=
  ⟨.postRec, 1, 1, 2, 2, 0, 1, 0, 2, Finset.Icc 0 1, {(1, 1)}, some (1, 1), [], []⟩

/-- TV-I2 second-branch closing read: the confirming W = 1 species the
`wordMidB` selection (1, 1) opens — D′ = e·g·D = 2·1·1 = 2 (the stride-2 read
DOUBLES the key degree), tag POST-INC by 2 ≤ e·g.  DISTINCT from `wordLast`
(D = 2 vs 1, tag postInc vs postRec): the two branches' closing reads carry
distinct Species data. -/
def wordLastB : Species :=
  ⟨.postInc, 2, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1, 1)}, none, [], []⟩

theorem succStep_wordHead_wordMidB : SuccStep 2 wordHead wordMidB :=
  (succStepB_iff 2 wordHead wordMidB).mp (by decide)

theorem succStep_wordMidB_wordLastB : SuccStep 2 wordMidB wordLastB :=
  (succStepB_iff 2 wordMidB wordLastB).mp (by decide)

/-- the second branch's catalogue word as a read map (junk `wordLastB` above
r = 2), mirroring `toyWord`. -/
def toyWordB : ℕ → Species
  | 0 => wordHead
  | 1 => wordMidB
  | _ => wordLastB

/-- TV-I2 carrier: the EXTENDED toy model — a `CanTreeModel` at the same
(n, p, f) = (2, 2, f₂) key with (at least) TWO branches whose closing reads
carry DISTINCT Species data (the cheap-extension candidate: branch 0 = the
transported G1 toy A word ⟨wordHead, wordMid, wordLast⟩ as in `toyCanModel`;
branch 1 = a second catalogue word with a different closing read).  Every law
field discharged by computation on actual letters, as in `toyCanModel`. -/
noncomputable def toyCanModelD : CanTreeModel 2 2 f₂ where
  Branch := Bool
  hTotal := ⟨false⟩
  len _ := 3
  hN1 := fun h => absurd h (by decide)
  datum η r := match η with
    | false => toyWord r
    | true => toyWordB r
  hRoot := fun η _ => by
    cases η <;> exact wordHead_rootAdmissible
  hStage := by
    intro η r hr
    have hr' : r + 1 < 3 := by exact_mod_cast hr
    have hr'' : r < 2 := by omega
    cases η <;> interval_cases r
    · exact succStep_wordHead_wordMid.1
    · exact succStep_wordMid_wordLast.1
    · exact succStep_wordHead_wordMidB.1
    · exact succStep_wordMidB_wordLastB.1
  hCoh := by
    intro η r hr
    have hr' : r < 3 := by exact_mod_cast hr
    cases η <;> interval_cases r
    · exact ⟨wordHead_rootAdmissible.2.1, wordHead_rootAdmissible.2.2⟩
    · exact ⟨succStep_wordHead_wordMid.2.1, succStep_wordHead_wordMid.2.2⟩
    · exact ⟨succStep_wordMid_wordLast.2.1, succStep_wordMid_wordLast.2.2⟩
    · exact ⟨wordHead_rootAdmissible.2.1, wordHead_rootAdmissible.2.2⟩
    · exact ⟨succStep_wordHead_wordMidB.2.1, succStep_wordHead_wordMidB.2.2⟩
    · exact ⟨succStep_wordMidB_wordLastB.2.1, succStep_wordMidB_wordLastB.2.2⟩
  hHalt := by
    intro η r hr hw
    have hr' : r < 3 := by exact_mod_cast hr
    cases η <;> interval_cases r
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · norm_num
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · norm_num
  verdict η := match η with
    | false => some Verdict.ep
    | true => some Verdict.z
  hVerdictPin := fun η _ _ _ => by cases η <;> rfl

/-- TV-I2 the DISCRIMINATING strong pin at the extended model: tauV reads
its Species argument (branch-reading, emitting {(1,1)} vs a second built
verdict), dict injective on the emitted values, cap := the closing-read
bound with `hcap` a REAL proof (agreement below cap covers the closing read
⇒ equal verdicts), htau by per-branch case analysis. -/
noncomputable def toyStrongPinD : StrongVerdictPin toyCanModelD where
  tauV s :=
    if s.D = 2 then MovesT.irrVerdict 2 1 (by norm_num) le_rfl
    else MovesT.irrVerdict 1 1 le_rfl le_rfl
  dict v :=
    if v = MovesT.irrVerdict 2 1 (by norm_num) le_rfl then Verdict.z
    else Verdict.ep
  htau := by
    intro η r h
    have h' : (3 : ℕ∞) = ((r + 1 : ℕ) : ℕ∞) := h
    have h3 : (3 : ℕ) = r + 1 := by exact_mod_cast h'
    have hr : r = 2 := by omega
    subst hr
    cases η
    · decide
    · decide
  hinf := fun η h => absurd (show (3 : ℕ∞) = ⊤ from h) (by decide)
  cap := 3
  hcap := by
    intro η η' hlen hagree
    cases η <;> cases η'
    · rfl
    · exact absurd (hagree 2 (by norm_num)) (by decide)
    · exact absurd (hagree 2 (by norm_num)) (by decide)
    · rfl

/-- TV-I2 (c2) ACROSS DISTINCT VERDICTS: the extended model realizes two
branches with DIFFERENT verdicts — the exactly-one clause is exercised
across distinct values, not at a constant (the A25 disclosure's first gap). -/
theorem toyCanModelD_discriminates :
    ∃ η η' : toyCanModelD.Branch,
      toyCanModelD.verdict η ≠ toyCanModelD.verdict η' :=
  ⟨false, true, by decide⟩

/-- TV-I2 tauV discrimination: the halting rule genuinely reads its Species
argument (the constant witness ignored it). -/
theorem toyStrongPinD_tau_discriminates :
    ∃ s s' : Species, toyStrongPinD.tauV s ≠ toyStrongPinD.tauV s' :=
  ⟨wordLast, wordLastB, by decide⟩

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
  intro η η' r r' h1 h2 hd
  have hr : r = 2 := by
    have h1' : (3 : ℕ∞) = ((r + 1 : ℕ) : ℕ∞) := h1
    have h3 : (3 : ℕ) = r + 1 := by exact_mod_cast h1'
    omega
  have hr' : r' = 2 := by
    have h2' : (3 : ℕ∞) = ((r' + 1 : ℕ) : ℕ∞) := h2
    have h3 : (3 : ℕ) = r' + 1 := by exact_mod_cast h2'
    omega
  subst hr; subst hr'
  cases η <;> cases η'
  · rfl
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · rfl

/-- TV-I2 (c3-b) REAL cap sensitivity (resolution (3)): verdicts are NOT
determined by branch length alone — the verdict map reads the word datum,
so `hcap`'s cap-truncated-agreement premise is load-bearing (at the constant
witness this statement is FALSE, certifying the strengthening is real). -/
theorem toyStrongPinD_cap_sensitive :
    ¬ ∀ (η η' : toyCanModelD.Branch),
      toyCanModelD.len η = toyCanModelD.len η' →
      toyCanModelD.verdict η = toyCanModelD.verdict η' := by
  intro hall
  exact absurd (hall false true rfl) (by decide)

end LeanUrat.MovesV
