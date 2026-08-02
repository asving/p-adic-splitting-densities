/-
SITE-EXH ADJUDICATION PROBE — `H1/SiteExhProbe.lean`
(hardest-first Tier 1 item 1, `docs/HARDEST_FIRST_ORDER_2026-08-08.md`; charge: the
open obligation SITE-EXH of `lean/notes/openmath/H1_BM2_2026-08-06.md` §S2 — "that
the three recorded carriers EXHAUST the engine's key-firing sites is NOT proved";
evidence base: the C-e fence exhibit, `lean/notes/openmath/BM2_TRACE_2026-08-02.md`
§C-e; ledger: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`).

## THE QUESTION

Is SITE-EXH — "every lift the engine fires factors through the recorded carriers:
LandingKey / historyCoherent key+recentering / readsOf-landing" — closable in the
CURRENT run architecture, or does closure require extending it?

## VERDICT: NEEDS-EXTENSION → **EXTENSION LANDED** (TruncatedRun carrier; disjoint box-face bridge)

[EXTENSION LANDED 2026-08-08 — ASVIN SIGN-OFF ledger 49b778e ("yeah go ahead" on
E-1..E-4 as displayed).  `H1/TruncatedRun.lean` compiles E-1 (`TruncRunFrom` +
`ReadsOfFrom`), E-2 (`moveWitness_standardLift`/`moveWitness_hosts`/
`moveWitness_hosts_readsOfFrom`), and E-4's fences (this file and
`ReadsOf`/`HistoryCoherent` byte-unchanged; no RG-2 lift).  The §3 residue row is
discharged there IN WIDENED FORM, at two displayed layers (layering per the
pre-commit Codex adversarial pass): `TowerMoveClosure'` — the row at the AS-BUILT
core-free widened target `OnRecordedCarrier ∨ OnTruncatedCarrier` — is a THEOREM,
and `siteExh_elimination' : ∀ fl : FiredLift p F, fl.Lands'` fires UNCONDITIONALLY
over this enumeration (junk-hostable towerMoves included); `TowerMoveClosureL` —
the row at the SIGNED core-binding carrier `OnTruncatedCarrierL`, hypothesis =
S9/S10's own `StageCoreL σ` calling convention — is ALSO a theorem.  The ORIGINAL
narrow-target row `TowerMoveClosure` and the conditional `siteExh_elimination`
stand below, byte-unchanged and still open/conditional, as the recorded-carrier
display.  E-3 (the D-ITER composition glue) is the follow-up unit [LANDED
2026-08-08 — `H1/GlueRun.lean`: structural glue + f-tie proved; the D-ITER carry
law enters only the displayed junction-bundle supplier, named open
`DIterJunctionSupplier`]; the box face (§6) is untouched.  The deviations of the as-built E-1 from the display below —
base-read bundle = dev + (LandingKey ∨ IsStandardLift) with forcing compiled for
clauses (iv)/(v) only, clauses (i)-(iii)/(vi) not-retained-with-reason; the
core-free kernel under the tagged `ReadsOfFrom` — are recorded with the full Codex
fold in `TruncatedRun.lean`'s header, with a STANDING RE-RATIFICATION ITEM for
Asvin on the layering.]

The closed `FiredLift` datatype COMPILES (§1 below — the honest constructor-level
enumeration, census under "THE CENSUS"), and the elimination CLOSES DEFINITIONALLY
for the three run-borne shapes (§3: `histNonrec_lands` / `histRec_lands` /
`readsOf_landing_lands` — they ARE the carriers).  It does NOT close for the two
remaining shapes, and the failures are exactly characterized:

* **`towerMove` (the C-e / truncated-run shape).**  The stage-level engine spine
  (`HC1.MoveWitness` = the S9_transStage/S10_recStage firing forms, `Tower.move`'s
  field type) fires with NO run attached.  Landing it on a recorded carrier
  requires HOSTING its stage as a node of a lawful history, and the current
  architecture supplies no host: `HistoryCoherent` pins node 0 to a DEGREE-1 frame
  (`base_deg_pin` below) and fences every interior non-recentering read to stride
  `e = 1` (`rg2_fence` below) — so a stage whose only genesis is an interior
  `e ≥ 2` increment has NO lawful host AT ITS OWN CLASSIFICAND.  This is not
  hypothetical: the traced REAL p = 3 quartic tower (BM2_TRACE §C-e, exact
  arithmetic + PARI) has its order-1 recentering behind an interior e = 2 read —
  the engine mathematically fires it, and no lawful full `ReadsOf` run on f can
  record it (numerics-backed refutation-at-nature of the f-tied closure; the
  compiled mechanism is the two fence lemmas).  The residue is the DISPLAYED row
  `TowerMoveClosure` (§3): the master elimination `siteExh_elimination` is proved
  CONDITIONAL on exactly that row — no sorry, the row is the adjudicated gap.
  The row is NOT vacuously false: `gate_flTower_lands` (§5) fires it on the RCW
  recentering move, which DOES host (in `RCW.H₃rc`).  It is NOT provable either:
  its ∀-form quantifies over junk-hostable and unhostable moves alike, and the
  only compiled run-suppliers on file are per-instance gates (U31/HK23/HK25/RCW).
* **`FiredLiftBox` (the base-face liftKey path).**  The classifier's box-face key
  producers `OM.B.liftKey` (level ring `ZMod (p^N)`) and
  `OM.LiftKeyExt.liftKeyExt` (unramified base ring `Oring p N g`) produce keys in
  DIFFERENT COEFFICIENT RINGS from the carrier vocabulary (`Polynomial ℤ_[p]`,
  `Stage p F`).  A `Lands` predicate is UNSTATEABLE for them — the probe records
  this as the type-forced SPLIT of the enumeration into `FiredLift` (engine face)
  and `FiredLiftBox` (box face), with the minimal bridge obligation displayed as
  `BoxKeyBridge` (§6).  This residue is DISJOINT from the run-architecture
  question (it is the M1 projective-bridge track).
* **No fourth engine-face shape was found** (census below) — the pass-3 §S6(iii)
  attack stays un-cashed; the datatype below is the compiled form of that claim
  and any new firing site must extend it (a visible, auditable event).

## THE CENSUS (the §S2 route-(2) constructor/call audit, grep-complete 2026-08-08)

Key-ASSERTING carriers wired into runs (the three recorded carriers, §S2 (a)/(b)/(c)):
* `HistoryCoherent` 4th conjunct, non-recentering leg — asserts `IsNodeLift νᵢ σᵢ₊₁.Φ`
  (+ RG-2 fence `νᵢ.e = 1`)                                   [`MovesC/Defs.lean:717`]
* `HistoryCoherent` 4th conjunct, recentering leg — asserts
  `IsRecenteringCore σᵢ σᵢ₊₁ center lift`                     [`MovesC/Defs.lean:717`]
* `ReadsOf`/`SideReads` clause (iv) — `LandingKey ν Φnext` at EVERY read, final
  included; `KeysLawful` is the same carrier restated          [`HC2/Defs.lean:280,320,333`]

Key-INSTALLING engine constructors (stage level, run-free — the escape face):
* `HC1.S9_transStage` (increment: child key := `Φhat`, `TransitionData.child_key`)
                                            [`HC1/S9_transStage.lean:81`; `Moves/DefsT.lean:147`]
* `HC1.S10_recStage` (recentering: child key := `σ.Φ − tt`)   [`HC1/S10_recStage.lean:376`]
* both packaged as `HC1.MoveWitness` (`inc`/`recenter`), the `Tower.move` field type
                                                              [`HC1/DefsTower.lean`]

Box-face key producers (the classifier engine proper):
* `OM.B.liftKey` (+ `childResidual` recursion through it)     [`OM/Classifier.lean:300`]
* `OM.LiftKeyExt.liftKeyExt`                                  [`OM/LiftKeyExt.lean:87`]

NON-firing key installations (audited, excluded with reasons):
* `RegradeOf` — KEY-PRESERVING (`σV.Φ = σ.Φ` is its first conjunct; compiled below as
  `regrade_key_preserving`)                                   [`MovesC/Defs.lean:631`]
* base seeds (`IsBaseStage`, `T1_baseStage`, gate stages `bStageP`/G1 toys) — the seed
  key is not fired by a read; runs pin it by the node-0 clause (`base_deg_pin`)
* `polOM.liftOf` — produces the recentering LIFT REALIZER (node datum consumed by
  `SideReads` (v)), not a key; the key it induces is asserted by `LandingKey`/
  `IsRecenteringCore` (carriers above)                        [`HC2/Defs.lean:166`]
* `MovesT.eligible` (W4-1 seam) — re-keys SideReads' clause bundle, same carrier shapes
* gate instances (U31, HK22/23/25, RCW, forge families) — instances of the run-borne
  shapes, not new shapes

## THE MINIMAL EXTENSION (DESIGN DISPLAY ONLY — an architecture decision for Asvin;
## nothing below implements it)

* **E-1 (the TruncatedRun carrier).**  `ReadsOfFrom (σ₀ : Stage p F) (hσ₀ : StageCoreL σ₀)
  (f₀ : Polynomial ℤ_[p]) (H : History p F) : Prop` — a run whose node-0 frame is the
  GIVEN lawful stage (`(H.nodes[0]).σ = σ₀` replaces the deg-1 pin; all interior
  clauses of `HistoryCoherent`, the RG-2 fence included, are RETAINED above the base
  read; the base read's own pair `(e₀, h₀)` is free), with the per-read `SideReads`
  bundle unchanged, read against σ₀-developments of the LOCAL classificand f₀.
* **E-2 (the landing corollary).**  Every `MoveWitness σ σ'` at a `StageCoreL σ` is the
  base read of a ONE-NODE truncated run (σ hosts as node 0 — the deg-1 pin is what
  blocked it; `Φnext := σ'.Φ` designated), so `towerMove` lands on the truncated
  landing carrier and `FiredLift.Lands` closes over the widened disjunction
  `OnRecordedCarrier ∨ OnTruncatedCarrier`.  (K0)-class consumers need no more.
* **E-3 (the f-tie).**  f-tied consumers compose truncated runs along the D-ITER
  iterated development (Tier-3 item 5(b) of the hardest-first order): a full run on f
  = truncated runs glued at interior e ≥ 2 reads — exactly the C-e tower's shape.
  The glue theorem is the extension's one genuinely new obligation.
* **E-4 (what E-1 must NOT do).**  Do not lift RG-2 globally (the FENCE-LIFT FLAG of
  `MovesD/R7_runRealizer.lean`: the (CR2) re-adjudication is a prerequisite of any
  fence lift); do not touch `ReadsOf`/`HistoryCoherent` (byte-unchanged; the carrier
  is ADDITIVE).  Hence the verdict NEEDS-EXTENSION, not repair-in-place.
* **Box face (disjoint).**  `BoxKeyBridge` (§6) + a stage-host for the lifted key —
  the M1 projective-bridge track; a run-architecture extension does not touch it.

## WHAT IS COMPILED HERE (all sorry-free; no new axioms; no existing statement touched)

`FiredLift`/`FiredLiftBox` (the closed enumerations) · `OnRecordedCarrier` (the §S2
(a)/(b)/(c) landing disjunction) · `FiredLift.Lands` · the three run-borne landing
theorems · `TowerMoveClosure` (the displayed residue ROW — carried, never asserted) ·
`siteExh_elimination` (the master elimination, conditional on exactly that row) ·
`rg2_fence` + `base_deg_pin` (the compiled C-e exclusion mechanism) ·
`regrade_key_preserving` (census closure) · non-vacuity gates for all four engine-face
constructors + `gate_flTower_lands` (the residue row fires at the RCW instance) ·
`BoxKeyBridge` (displayed box-face residue, stated not asserted).

WHAT IS NOT CLAIMED: no engine-wide firing status beyond the recorded carriers
(SITE-EXH stays OPEN — this probe adjudicates its closure ROUTE); no truncated-run
carrier exists yet (E-1..E-4 are a design display) [SUPERSEDED 2026-08-08: the
carrier now exists — `H1/TruncatedRun.lean`, see the verdict block above; THIS
file's own claims are unchanged]; the C-e refutation-at-nature is
numerics-backed (BM2_TRACE §C-e), not compiled — compiling it needs the real quartic
tower formalized, out of probe scope by charter.
-/
import LeanUrat.Scaffold.HDischarge.H1.RCWitness
import LeanUrat.HC1.DefsTower
import LeanUrat.HC2.U31_gateReadsOf
import LeanUrat.OM.Classifier
import LeanUrat.OM.LiftKeyExt

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesJ

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ### §1 — the closed firing enumeration (engine face)

One constructor per census shape.  The three run-borne constructors carry their run
and site; `towerMove` carries the stage-level engine's own move type
(`HC1.MoveWitness` — `inc` = S9/TransHyp increments, `recenter` = S10 recenterings),
exactly what `Tower.move` threads.  CLOSEDNESS is the census claim: any new firing
site in the corpus must add a constructor here (auditable). -/

/-- **The engine-face fired lift** — the closed enumeration of the corpus's
key-firing shapes (census in the file header).  Type-valued: constructors carry
their site data. -/
inductive FiredLift (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] : Type u where
  /-- an interior NON-RECENTERING transition of a coherent recorded history
  (`HistoryCoherent` 4th conjunct, non-recentering leg — carrier §S2 (a)) -/
  | histNonrec (H : History p F) (hH : HistoryCoherent H) (i : ℕ)
      (hi1 : i + 1 < H.nodes.length)
      (hspec : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species ≠ ReadSpecies.recentering)
  /-- an interior RECENTERING transition of a coherent recorded history
  (`HistoryCoherent` 4th conjunct, recentering leg — carrier §S2 (b)) -/
  | histRec (H : History p F) (hH : HistoryCoherent H) (i : ℕ)
      (hi1 : i + 1 < H.nodes.length)
      (hspec : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species = ReadSpecies.recentering)
  /-- a read of a lawful `ReadsOf` run firing its designated landing key
  (`SideReads` clause (iv) — carrier §S2 (c); the FINAL read included) -/
  | runLanding (n : ℕ) (f : Polynomial ℤ_[p]) (H : History p F)
      (hRO : ReadsOf p F n f H) (i : ℕ) (hi : i < H.nodes.length)
  /-- a STAGE-LEVEL engine move (the S9/S10 firing forms, `Tower.move`'s type):
  fires with NO run attached — THE escape face this probe adjudicates -/
  | towerMove (σ σ' : Stage p F) (mw : HC1.MoveWitness σ σ')

/-! ### §2 — the recorded-carrier landing target (the §S2 (a)/(b)/(c) display) -/

/-- **`OnRecordedCarrier σ Φ'`** — the fired pair (site stage σ, produced key Φ')
appears at one of the three RECORDED carriers: (a) an interior non-recentering
transition of a coherent history at a node carrying σ, landing Φ' as the child frame
key; (b) ditto recentering; (c) a designated landing key of a read of a lawful
`ReadsOf` run at a node carrying σ.  This is the DISJUNCTION the SITE-EXH display
(`H1_BM2_2026-08-06.md` §S2) names; rev-0's sin was DEFINING "fired" as this
predicate — here it is the landing TARGET, and `FiredLift` is the separate honest
domain. -/
def OnRecordedCarrier (σ : Stage p F) (Φ' : Polynomial ℤ_[p]) : Prop :=
  (∃ (H : History p F) (_ : HistoryCoherent H) (i : ℕ) (hi1 : i + 1 < H.nodes.length),
      (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species ≠ ReadSpecies.recentering ∧
      (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ = σ ∧ (H.nodes[i+1]'hi1).σ.Φ = Φ') ∨
  (∃ (H : History p F) (_ : HistoryCoherent H) (i : ℕ) (hi1 : i + 1 < H.nodes.length),
      (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species = ReadSpecies.recentering ∧
      (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ = σ ∧ (H.nodes[i+1]'hi1).σ.Φ = Φ') ∨
  (∃ (n : ℕ) (f : Polynomial ℤ_[p]) (H : History p F),
      ReadsOf p F n f H ∧
      ∃ (i : ℕ) (hi : i < H.nodes.length),
        (H.nodes[i]'hi).σ = σ ∧
        ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
          IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd ∧ SideReads (H.nodes[i]'hi) B Nd Φ')

/-- **The landing predicate**, per constructor: the firing's own (site stage,
produced key) land on a recorded carrier.  `runLanding`'s key lives inside the run's
∃ (Prop), so its landing is stated existentially at the designated key, pinned to
the child frame at interior reads — the shape of `readsOf_landing_K0`'s conclusion. -/
def FiredLift.Lands : FiredLift p F → Prop
  | .histNonrec H _ i hi1 _ =>
      OnRecordedCarrier ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ) ((H.nodes[i+1]'hi1).σ.Φ)
  | .histRec H _ i hi1 _ =>
      OnRecordedCarrier ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ) ((H.nodes[i+1]'hi1).σ.Φ)
  | .runLanding _ _ H _ i hi =>
      ∃ Φnext : Polynomial ℤ_[p],
        (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
        OnRecordedCarrier ((H.nodes[i]'hi).σ) Φnext
  | .towerMove σ σ' _ => OnRecordedCarrier σ σ'.Φ

/-! ### §3 — the elimination: what closes, and the exact residue -/

/-- Run-borne shape (a) lands — definitionally (it IS carrier (a)). -/
theorem histNonrec_lands (H : History p F) (hH : HistoryCoherent H) (i : ℕ)
    (hi1 : i + 1 < H.nodes.length)
    (hspec : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species ≠ ReadSpecies.recentering) :
    OnRecordedCarrier ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ) ((H.nodes[i+1]'hi1).σ.Φ) :=
  Or.inl ⟨H, hH, i, hi1, hspec, rfl, rfl⟩

/-- Run-borne shape (b) lands — definitionally (it IS carrier (b)). -/
theorem histRec_lands (H : History p F) (hH : HistoryCoherent H) (i : ℕ)
    (hi1 : i + 1 < H.nodes.length)
    (hspec : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species = ReadSpecies.recentering) :
    OnRecordedCarrier ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ) ((H.nodes[i+1]'hi1).σ.Φ) :=
  Or.inr (Or.inl ⟨H, hH, i, hi1, hspec, rfl, rfl⟩)

/-- Run-borne shape (c) lands — definitionally (it IS carrier (c)): every read of a
lawful run has a designated landing key, interior-pinned, on the carrier. -/
theorem readsOf_landing_lands (n : ℕ) (f : Polynomial ℤ_[p]) (H : History p F)
    (hRO : ReadsOf p F n f H) (i : ℕ) (hi : i < H.nodes.length) :
    ∃ Φnext : Polynomial ℤ_[p],
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      OnRecordedCarrier ((H.nodes[i]'hi).σ) Φnext := by
  obtain ⟨B, Nd, Φnext, hdev, hpin, hside⟩ := hRO.2.2.2 i hi
  exact ⟨Φnext, hpin,
    Or.inr (Or.inr ⟨n, f, H, hRO, i, hi, rfl, B, Nd, hdev, hside⟩)⟩

/-- **THE RESIDUE ROW (the adjudicated gap — carried, never asserted).**  Closure of
the stage-level engine face: every `MoveWitness` firing lands on a recorded carrier.
STATUS (this probe's finding): NOT provable in the current architecture (no general
run-supplier exists; only per-instance gates), NOT vacuously false
(`gate_flTower_lands` fires it at the RCW recentering move), and its f-TIED
refinement is REFUTED AT NATURE by the C-e exhibit (BM2_TRACE §C-e: a real tower's
recentering behind an interior e = 2 read has no lawful host on its own f — the
mechanism is `rg2_fence` + `base_deg_pin` below).  The honest closure route is the
ADDITIVE TruncatedRun carrier (header, E-1..E-4). -/
def TowerMoveClosure (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] : Prop :=
  ∀ (σ σ' : Stage p F), HC1.MoveWitness σ σ' → OnRecordedCarrier σ σ'.Φ

/-- **THE MASTER ELIMINATION** — SITE-EXH over the closed enumeration, adjudicated:
the three run-borne constructors are discharged UNCONDITIONALLY; the stage-level
constructor is discharged by exactly the displayed residue row.  SITE-EXH closure in
the current architecture ⟺ `TowerMoveClosure` (+ the box face, which cannot even be
stated — §6).  No sorry: the gap is the ROW, visible in the signature. -/
theorem siteExh_elimination (hMove : TowerMoveClosure p F) :
    ∀ fl : FiredLift p F, fl.Lands := by
  intro fl
  cases fl with
  | histNonrec H hH i hi1 hspec => exact histNonrec_lands H hH i hi1 hspec
  | histRec H hH i hi1 hspec => exact histRec_lands H hH i hi1 hspec
  | runLanding n f H hRO i hi => exact readsOf_landing_lands n f H hRO i hi
  | towerMove σ σ' mw => exact hMove σ σ' mw

/-! ### §4 — the compiled C-e exclusion mechanism (why the strict tower leg fails
at nature)

The BM2_TRACE §C-e argument, formalized at its two load-bearing clauses: any lawful
host history (i) starts at a degree-1 frame and (ii) carries no interior
non-recentering read of stride e ≥ 2.  A stage whose only genesis is an interior
e ≥ 2 increment (the traced quartic's Φ₁-frame stage) therefore hosts NOWHERE on its
own classificand — its subsequent recentering fires OFF every recorded carrier.
(The at-instance refutation itself needs the real tower formalized — numerics-backed
at BM2_TRACE §C-e, exit 0, PARI-confirmed; out of probe scope by charter.) -/

/-- **The RG-2 recording fence, extracted**: every interior non-recentering read of
a coherent history has stride `e = 1` (the HK-06 disclosed wiring-scope
restriction, `MovesC/Defs.lean` `HistoryCoherent` 4th conjunct). -/
theorem rg2_fence (H : History p F) (hH : HistoryCoherent H) (i : ℕ)
    (hi1 : i + 1 < H.nodes.length)
    (hspec : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species ≠ ReadSpecies.recentering) :
    (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).e = 1 := by
  obtain ⟨-, -, -, hstep⟩ := hH
  obtain ⟨-, hnonrec, -, -, -, -, -⟩ := hstep i hi1
  exact (hnonrec hspec).1

/-- **The node-0 degree pin, extracted**: every coherent history starts at a
degree-1 frame (`HistoryCoherent` 1st conjunct) — the clause barring truncated
starts at deeper frames. -/
theorem base_deg_pin (H : History p F) (hH : HistoryCoherent H)
    (h0 : 0 < H.nodes.length) : (H.nodes[0]'h0).σ.Φ.natDegree = 1 :=
  hH.1 h0

/-- Census closure: the read REGRADE is key-preserving (`σV.Φ = σ.Φ` is `RegradeOf`'s
first conjunct) — a stage creation, NOT a lift firing; hence no `FiredLift`
constructor for it. -/
theorem regrade_key_preserving (σ : Stage p F) (estar hstar : ℕ) (σV : Stage p F)
    (h : RegradeOf σ estar hstar σV) : σV.Φ = σ.Φ :=
  h.1

/-! ### §5 — non-vacuity gates (every constructor inhabited on compiled instances;
the residue row fires at the RCW instance) -/

/-- Gate instance (a): H₃rc's interior transition 0 → 1 (root read, non-recentering). -/
noncomputable def flNR : FiredLift 2 F4 :=
  .histNonrec RCW.H₃rc RCW.coherent_H₃rc 0
    (by rw [RCW.H₃rc_len]; omega)
    (by intro hcontra; exact ReadSpecies.noConfusion hcontra)

/-- Gate instance (b): H₃rc's interior transition 1 → 2 (THE interior recentering). -/
noncomputable def flRC : FiredLift 2 F4 :=
  .histRec RCW.H₃rc RCW.coherent_H₃rc 1
    (by rw [RCW.H₃rc_len]; omega)
    rfl

/-- The U31 run witness, extracted from the public gate `gate_readsOf_inert2`
(the in-file `readsOf_fq` is private). -/
private noncomputable def u31H : History 2 F4 := gate_readsOf_inert2.choose

private noncomputable def u31f : Polynomial ℤ_[2] :=
  gate_readsOf_inert2.choose_spec.choose

private lemma u31len : u31H.nodes.length = 1 :=
  gate_readsOf_inert2.choose_spec.choose_spec.1

private lemma u31RO : ReadsOf 2 F4 2 u31f u31H :=
  gate_readsOf_inert2.choose_spec.choose_spec.2.2

/-- Gate instance (c): U31's compiled `ReadsOf` run (root-only inert quadratic). -/
noncomputable def flRun : FiredLift 2 F4 :=
  .runLanding 2 u31f u31H u31RO 0 (by rw [u31len]; omega)

/-- Gate instance (tower): the RCW recentering move — S10's constructed
`IsRecenteringCore` + child `StageCoreL`, packaged as the engine's own move type. -/
noncomputable def mwRC : HC1.MoveWitness HK25.σ₁rec RCW.σ₂rc :=
  .recenter RCW.rcCenter RCW.rcLift RCW.recCore RCW.score₂

/-- Gate instance (tower), as a fired lift. -/
noncomputable def flTower : FiredLift 2 F4 := .towerMove HK25.σ₁rec RCW.σ₂rc mwRC

/-- GATE (a) lands. -/
theorem gate_flNR_lands : flNR.Lands :=
  histNonrec_lands RCW.H₃rc RCW.coherent_H₃rc 0
    (by rw [RCW.H₃rc_len]; omega)
    (by intro hcontra; exact ReadSpecies.noConfusion hcontra)

/-- GATE (b) lands. -/
theorem gate_flRC_lands : flRC.Lands :=
  histRec_lands RCW.H₃rc RCW.coherent_H₃rc 1
    (by rw [RCW.H₃rc_len]; omega) rfl

/-- GATE (c) lands. -/
theorem gate_flRun_lands : flRun.Lands :=
  readsOf_landing_lands 2 u31f u31H u31RO 0 (by rw [u31len]; omega)

/-- **GATE (tower): the residue row FIRES at the RCW instance** — the S10-fired move
`mwRC` lands on carrier (b) via H₃rc's interior recentering at i = 1 (node 1 carries
σ₁rec; node 2's frame key is σ₂rc.Φ).  So `TowerMoveClosure` is not vacuously false;
its general form is the open residue (header verdict). -/
theorem gate_flTower_lands : flTower.Lands := by
  show OnRecordedCarrier HK25.σ₁rec RCW.σ₂rc.Φ
  exact Or.inr (Or.inl ⟨RCW.H₃rc, RCW.coherent_H₃rc, 1,
    by rw [RCW.H₃rc_len]; omega, rfl, rfl, rfl⟩)

/-! ### §6 — the box face: the enumeration SPLITS on coefficient-ring type

The classifier's own key producers live over the box rings, not `ℤ_[p]` — a `Lands`
predicate against the recorded carriers is UNSTATEABLE for them (no ring map is even
wired from `ZMod (p^N)` back to `ℤ_[p]`; only the forward reductions exist).  The
compiled record of this finding is the SEPARATE datatype below; the minimal bridge
obligation (the M1 projective-bridge track, DISJOINT from the run-architecture
extension) is displayed as `BoxKeyBridge` — stated, not asserted. -/

/-- **The box-face fired lift** — the classifier engine's key-producing shapes
(`OM.B.liftKey` at the prime box; `OM.LiftKeyExt.liftKeyExt` at the unramified
extension box).  Kept a SEPARATE type: its produced keys inhabit
`Polynomial (ZMod (p^N))` / `Polynomial (Oring p N g)`, so `FiredLift.Lands`'s
vocabulary cannot receive them (the type-forced split IS the §S6(iii) finding for
this face). -/
inductive FiredLiftBox (p : ℕ) [Fact p.Prime] : Type where
  /-- `OM.B.liftKey p N ψ` — the base-face key lift of a residual factor ψ -/
  | baseFace (N : ℕ) (ψ : Polynomial (ZMod p))
  /-- `OM.LiftKeyExt.liftKeyExt` — the unramified-extension key lift -/
  | extFace (N : ℕ) (g : Polynomial (ZMod (p ^ N))) (hgm : g.Monic) (hN : 0 < N)
      (Ψ : Polynomial (OM.UnramifiedBase.resField p N g hN))

/-- The base-face fired key, at its OWN type (the level-N box ring) — the accessor
whose codomain exhibits the mismatch with `OnRecordedCarrier`'s `Polynomial ℤ_[p]`. -/
noncomputable def FiredLiftBox.boxLevel : FiredLiftBox p → ℕ
  | .baseFace N _ => N
  | .extFace N _ _ _ _ => N

/-- **THE BOX-FACE RESIDUE (displayed, not asserted)**: every base-face fired key is
the level-N shadow of an integral key.  This is the KEY-TRANSPORT half of the box
face's factoring; the other half (a lawful STAGE HOST for the lifted key) is the M1
projective-bridge track.  Neither is claimed here. -/
def BoxKeyBridge (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (N : ℕ) (ψ : Polynomial (ZMod p)), ∃ Φ : Polynomial ℤ_[p],
    Φ.Monic ∧ Φ.map (PadicInt.toZModPow N) = LeanUrat.OM.B.liftKey p N ψ

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.siteExh_elimination
#print axioms LeanUrat.Scaffold.HDischarge.H1.rg2_fence
#print axioms LeanUrat.Scaffold.HDischarge.H1.base_deg_pin
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_flNR_lands
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_flRC_lands
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_flRun_lands
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_flTower_lands
#print axioms LeanUrat.Scaffold.HDischarge.H1.regrade_key_preserving
