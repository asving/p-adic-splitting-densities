# Verdict — unit PK12 (packaging-route nodes PK-1 + PK-2)

Date: 2026-08-26.  Plan: `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` (Route A, §4
diffs).  Elaboration authority: `leanfinal/scratch/U15_check.lean`.  Scope per the unit
brief: PK-1 (carrier retype) + PK-2 read as "repair EVERY consumer of the retyped carrier"
— which folds the plan's PK-2..PK-6 leanfinal work (view binders, C130pk's factored map,
CC-17's constructors, CC-18's socket bodies, SG's funnel) into this unit.  NOT touched:
`leanspec/` (the I.10a/b socket re-sign stays a later node), roll-up import lists
(`Uniformity/ChapC.lean` etc.), `C130k.lean` (the un-split `NodePointSource` survives as
the U13 quarantine record), and the plan/scratch documents.

## VERDICT: ENACTED — all four gate builds green, every footprint Lean-core, zero sorry,
zero new axiom, both non-swallowing grep-teeth pass (rg/grep exit 1).

## Build results (the four gates)

| gate | result |
|---|---|
| `lake build Uniformity.ChapC` (leanfinal) | **green** — "Build completed successfully (8804 jobs)"; only pre-existing warning: `Uniformity/ChapC.lean:1` copyright-header linter note (roll-up file, untouched) |
| `lake build Uniformity.ChapI` (leanfinal) | **green** — "Build completed successfully (8710 jobs)" |
| `cd leanspec && lake build Leanspec.ChapC` | **green** (leanspec imports the FULL `Uniformity` root, so this gate rebuilt the entire leanfinal library against the retype) |
| `cd leanspec && lake build Leanspec.ChapI` | **green** — combined leanspec build "Build completed successfully (9278 jobs)"; leanspec sources untouched (its only `ChainRealization` mention is prose) |

AxChk audit: `lake env lean` on all 12 touched/new files — every `#print axioms` row is
exactly `[propext, Classical.choice, Quot.sound]` (or "does not depend on any axioms");
no `sorryAx`, no custom axiom anywhere.

## PK-1 — per-file diff summary

* **NEW `leanfinal/Uniformity/ChapC/C130k2.lean`** (imports C130st): `SplitNodePointSource`
  + `legalPoint`/`legalPoint_mem`/`stageCarrier` moved VERBATIM (docstrings included) from
  C130s17's SF1 section into namespace `Uniformity.Density.Tower`, per plan §4.1.  Dated
  [PK-1/U15] module note.  AxChk: 4 rows, Lean-core.
* **`C130fg.lean`** — `ChainRealization` retyped per §4.1 (scratch `ChainRealizationV2`,
  landed under the original name): `(e' f' u' : ℕ)` params REMOVED; `fgmn`/`fgmnLaws`/
  `grade_compat`/`letter_compat` fields REMOVED; new params `(E : Type uE) [fieldE :
  Field E]`; `node : SplitNodePointSource (L := L) W E receiver keys`.
  `FGMNSourceData`/`FGMNSourceLaws` byte-UNTOUCHED.  Dated notes added; imports +C130k2.
  ONE recorded micro-deviation from the scratch signature: the `Field E` instance binder is
  NAMED (`[fieldE : Field E]`, same elaborated type) so C130s18's existential socket bodies
  can pass it explicitly (`(fieldE := fE)`) — the named-instance pattern the file already
  uses for `dom`/`dvr`.
* **`C130in.lean`** — `RealizedInput` binder diff per §4.3 (scratch `RealizedInputV2`):
  `{n e' f' u'}` → `{n}`, `{E : Type uE} [Field E]` added, carrier arg `core.T Kt E L`;
  all five fields and every downstream theorem byte-stable.

## PK-2 — the ripple table (every consumer of the retyped carrier)

| file | repair | statements |
|---|---|---|
| `C130th.lean` (CC-7) | whole threshold layer retyped `NodePointSource` → `SplitNodePointSource` (+`{E}` binder, import C130k2) | byte-unchanged mod binder; all proofs byte-stable |
| `C130pt.lean` (CC-9) | layer retyped to split; `legalPoint`/`legalPoint_mem` DELETED here (they moved to C130k2 — one definition, no drift); teeth binders retyped | byte-unchanged mod binder |
| `C130cr.lean` (CC-10) | canonical-read layer + teeth retyped; one qualified `rw [NodePointSource.canonicalRead_generatorWord]` → `SplitNodePointSource.…` | byte-unchanged mod binder |
| `C130ar.lean` (CC-11) | arena layer + both teeth sections retyped; standalone helpers (`arenaKerProj`, norm sections) untouched; CC-11 audit grep-tooth re-verified (exit 1) | byte-unchanged mod binder |
| `C130vw.lean` (CC-12) | carrier binder block only (`{e' f' u'}` dropped, `{E}` added); one qualified `NodePointSource.towerReadFamily0_live` → split | all four view Props + producing equalities byte-unchanged |
| `C130pk.lean` (CC-16) | `ChainRealization.toCalculus`/`chainRealization_calculus_nonempty` RETIRED (deleted; docstrings re-point); factored `fgmnCalculusOf` + `fgmn_model_calculus_nonempty` landed per §4.2 (scratch §2, field-for-field); 9 anti-drift rfl teeth restated at the factored map; still a `def`, NO instance declared | new pair per plan display |
| `C130s17.lean` (CC-17) | SF1 section replaced by move-note + `export Uniformity.Density.Tower (SplitNodePointSource)` (alias, not a copy — no ambiguity, resolves to the same constant); `toChainRealization ev lf` → `toCarrier` (NO premises); `calculusNonempty` deleted (role moved to sg's discharge + pk's factored theorem); `realizedInput`/`s2RealizedInput` drop `ev`/`lf` (all three dictionary fields still `rfl`); `LegacyEvaluation`/`LegacyFGMN`/`withLegacy` KEPT with QUARANTINE notes (refutation record, off every packaging path) | frontier structure + SF-4 tooth byte-unchanged |
| `C130s18.lean` (CC-18) | §4.4 enacted: socket bodies' `∃ (e' f' u' : ℕ) … ChainRealization … e' f' u'` → `∃ (E : Type uE) (fE : Field E) … ChainRealization … (fieldE := fE) core.T Kt E L`; view conjuncts unchanged; S2 gate theorems drop `ev`/`lf`; audit re-run at the split node (`twistNode`/`twistRealization` retyped, FGMN legs gone); lint destructurings updated; leanspec sockets untouched | grep-tooth passes (exit 1) |
| `C130sg.lean` (SG) | funnel stages 1/3/4a/4b re-run `ev`/`lf`-FREE (conditional on exactly `w : S2LevelOneThreshold` + `IsAdicComplete`); stage 2 replaced by ★ `s2AnchorCalculus` + ★ `s2_calculus_discharge : Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5)` — UNCONDITIONAL, Lean-core, with the two operator anti-drift rfl pins (`Rres = s2NormRes`, `KP = S2KeyPoly`); BOTH emptiness theorems (`s2Frontier_legacyEvaluation_isEmpty`, `s2LegacyFGMN_landed_empty`) retained statement-verbatim | discharge per plan §1/§7 |

## Sites the diff didn't cover — minimal repairs, RECORDED

1. **`C130st.lean` — NO edit**, though the plan's PK-2 row lists it.  Structural reason:
   C130k2's `stageCarrier` (the plan-mandated verbatim move) needs C130st's
   `DeepTower.fhat`/`Dcum_eq_ehat_mul_fhat`/`Dcum_pos`, so C130st is UPSTREAM of the split
   structure and cannot be retyped to it (import direction); retyping would also clash with
   C130k2's moved `stageCarrier`.  Its un-split CC-5 layer survives as (a) the quarantined
   `NodePointSource`'s layer and (b) the supply for C130s6/C130np1's conditional
   `stageCarrier_*_eq_s2` ties, which therefore compile UNCHANGED.
2. **Universe pinning in C130s18** (not in the plan's §4.4 display, forced by elaboration):
   the four socket Props get explicit universe lists (`.{uE', uG', uKt', uL'}`) and the
   consuming theorems annotate the new existential-ambient universe at application sites
   (e.g. `CanonicalLadderConfigData.{uE, uG, uKt, uL}`, S2/sg sites `.{0, uG, 0, uL}`) —
   otherwise the `∃ (E : Type uE)` universe is an unconstrained metavariable.  Same
   mechanism in C130sg's stage-4 statements.  Diff-spirit: the plan's `∃ (E : Type uE)`
   kept universe-polymorphic, only made inferable.
3. **Named instance binders** `[fieldE : Field E]` in C130fg (see PK-1 above) — the
   in-repo `dom`/`dvr` pattern, needed because ∃-bound instance hypotheses are not local
   instances.
4. **`C130pt`'s `legalPoint`/`legalPoint_mem` deleted** rather than duplicated (they moved
   to C130k2 under the same `SplitNodePointSource` namespace; a retyped copy in C130pt
   would be a name clash).  Their AxChk rows moved to C130k2's footer.

## What is now non-vacuously true (plan §7, machine-checked this unit)

* `C130sg.s2_calculus_discharge : Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5)` —
  unconditional, Lean-core: the first genuinely inhabited `FGMNCalculus` hypothesis carrier.
* `C130sg.s2Frontier_ladder_socket` / `s2Frontier_deepTwist_socket` (and the I.10b→I.10a
  refinement at the S2 instance): both I.10-shaped socket applications at the concrete
  `keyAt 2 + 1` occurrence, conditional on exactly `w : S2LevelOneThreshold` +
  `IsAdicComplete` — no provably-empty premise anywhere on the path.
* NOT claimed: any GENTOW consumer conclusion at S2 (plan §6 rows 2/4; depth-2 deferred to
  the corrected-parameter μ₃ campaign).

## Notes for later nodes

* The leanspec I.10a/b re-sign (later node, not this unit) now targets C130s18's §4.4
  bodies as amended above (including the explicit-universe shape and `(fieldE := fE)`).
* `scratch/U15_check.lean` was NOT edited (it is the historical elaboration authority); it
  will no longer elaborate against the enacted corpus (e.g. its own `fgmnCalculusOf`
  duplicate and V2 names) — expected for a consumed scratch authority.
* PK-7 (PROJECT_STATE + review-list rows §6) remains open, per the node plan.
