/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger
import LeanUrat.MovesU.BridgeB2_stateNe
import LeanUrat.MovesU.BridgeD4_vtLaws
import LeanUrat.MovesU.BridgeD5_transferRow
import LeanUrat.MovesU.BridgeD13_sliceFinite

/-!
# BP1 group F — the hypothesis packs (IB-F1, IB-F2) + the cl7_slice wiring (IB-F6)

E-phase skeletons per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.7 / §4
group F, cluster BP1-c10.  File name per the blueprint's §4 prescription
("New files: … BridgeKernels.lean + BridgeMk.lean (F)").  Units in this file:

* IB-F1  `BridgePre` — the p-UNIFORM named-premise pack (hdet, hStateNe);
         statement-only, ADJ (ratification: BRIDGE_ADJUDICATIONS Q3, RATIFIED).
* IB-F2  `BridgeKernelsCtor` + `BridgeKernels` — THE KERNEL PACK, split into its
         two internal layers with the exact dependency order FIXED (the §3.7
         ordering charge is assigned to this unit); statement-only, ADJ — the
         area's honesty ledger (Codex-audit magnet).
* IB-F6  `bridge_cl7_slice` — the `slice_bound` row → `UInstance.cl7_slice`
         field wiring.

## THE DEPENDENCY ORDER (the §3.7 charge: "The E-phase writer fixes the exact
dependency order; the blueprint's invariant is only: NO field mentions an
object constructed after it")

The §3.7 display lists TWELVE rows.  This file compiles the internal split:

    [above the line — construction-feeding rows, `BridgeKernelsCtor`]
      transfer      (†6)  — consumed by IB-D8 (canonical_stable), IB-D15
                            (vt_real), IB-D16 (vt_surj), treeOf coherence
      slice_finite  (†9)  — ROW DELETED 2026-07-30: the R6 pigeonhole probe
                            LANDED (BridgeD13's `realizes_finite` +
                            `realizedSelf_slice_finite`, PROVED) — the row is
                            now THE PROVED THEOREM `bridge_slice_finite`
                            (below), consumed by IB-D14 (`bridgeFibers`'s
                            thrSlice argument, through IB-D13's `sliceFinset`)
        ↓  [the D/B/C/E-group constructions: X (D7/D8/D9a/D11), F (D3/D4/D12/
            D13/D14), treeOf/thr_le (D17), Tpin (D18 at A11's dictionary),
            D (B8), Dpin (B10), solve (C1 — landed, `bridgeSolve`),
            bridge (E-group, Q2-gated)]
      count_tie     (†9)  — the [3t]/TREE-N row: NOT a field of either pack;
                            it is the THIRD FIELD of the assembled `TreeSeam`
                            (`TreeSeam.count_tie`, DefsLedger.lean:235), so in
                            this parametric architecture it rides the `seam`
                            binder VISIBLY (D17 supplies only treeOf/thr_le;
                            the wiring carries count_tie as the open
                            hypothesis completing the seam — never proved,
                            never hidden).  Q7 ADJUDICATED: stays a named row
                            (discharge chain IB-D20/D21 off the default path).
        ↓
    [below the line — ledger rows over the constructed objects, `BridgeKernels`]
      slice_bound · series_tie · env_tendsto · vp_sound · sibjc · cl6 ·
      cl11_ksub · cl17 · cl19_rep
        ↓
    IB-F3 `bridgeCapstoneLedger` → IB-F4 `mkUInstance` → IB-F5 `theoremU_fired`
    (BridgeMk.lean).

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase rules):
1. The §3.7 sketch types the pack "over the CONSTRUCTED X := bridgeClassifier…,
   F := bridgeFibers…, seam, Tpin".  The construction units live in
   concurrently-writing sibling clusters and are themselves PARAMETRIC
   (BridgeD11/D14/D17/D18 headers: "IB-F4 instantiates"), so `BridgeKernels`
   binds the constructed objects as PARAMETERS (X, F, seam, Tpin) — the fleet's
   standing resolution (BridgeD13 precedent: "the generic form loses nothing —
   the wiring instantiates it at the carrier").  The final wiring instantiates
   them at the D/B/C/E-group constructions named above; the pack's fields are
   then EXACTLY the §3.7 ledger rows at those objects.
2. `transfer` and `slice_finite` CANNOT be fields of the same structure that
   binds the constructed objects (they feed those constructions — the §3.7
   ordering invariant), so the split is compiled as the separate
   construction-side pack `BridgeKernelsCtor`, stated CONCRETELY at IB-D3/D4's
   landed carrier (`bridgeTree`/`bridgeThr`) and IB-D5's landed `TransferRow`.
   [2026-07-30 UPDATE: `slice_finite` has since LEFT the pack — R6 probe
   success; it is the PROVED `bridge_slice_finite` below, and `transfer` is
   the pack's sole remaining row.]
   `BridgeKernelsCtor` is consumed by the D-group constructions, NOT by
   `mkUInstance` (whose binders already carry the constructions' outputs) — so
   `theoremU_fired`'s premise surface stays exact (no unused row).
3. `BridgeKernelsCtor` is parametric in the (†3) box dictionary `boxeq`
   (mirroring IB-D5's own recorded resolution); the wiring instantiates it at
   `Tpin.boxeq` (= IB-A11's `boxEquivD` through IB-D18's assembly), so the
   transfer row's dictionary IS the pinned one — no second dictionary.
4. NO `zp` catch-all row (blueprint REVISION 2, Codex finding 5 APPLIED): the
   ZpBridge is a CONSTRUCTED binder of the wiring (group E proves all five
   fields outright, post-Q2); a Group-E stall converting a ZpBridge law into a
   new NAMED row is an orchestrator adjudication (fence event), never a
   catch-all here.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-! ## IB-F1 — the p-uniform named-premise pack -/

/-- IB-F1: `BridgePre` — the p-UNIFORM pack of NAMED WARRANTED HYPOTHESES,
    bound BEFORE any construction (blueprint §3.7; G2).  Both rows RATIFIED as
    named premises at `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` Q3
    (statement-gaining-named-hypothesis events under the campaign's scoping
    authority).
    * `hdet` — the symbolic ℚ(q) determinant nonvanishing (†10a), p-INDEPENDENT.
      WARRANT: it is (r1)'s symbolic face — `RegPin.detHyp` DERIVES it from
      (REG-p) at any single prime (DefsLedger.lean:536); carrying it p-uniformly
      merely asserts (REG-p) holds somewhere, which `theoremU`'s consumer
      supplies anyway.  Feeds `bridgeSolve C hdet` (IB-C1, landed) and the
      roster's dite fields (IB-B9).
    * `hStateNe` — per-block state nonemptiness on the operative range (†4b),
      stated as IB-B2's `HStateNe` (the three consumers B2/F1/B8 speak ONE
      sentence).  WARRANT: the note's block table always contains the entrance
      state of block e — §S-RESUM's roster is per-block nonempty by
      construction; MOVES ledger rows CL-5/CL-1 quantify over it.  NOT derivable
      from the carried pack (IB-B2's E-phase interface audit, executed
      2026-07-30); IB-B2's prover-phase derivation attempt runs FIRST (Q3) —
      if it closes, this row DROPS and the area re-plans (fence event).
      Feeds `bridgeRegData`'s `instBiNe`/`blockDim_pos` (IB-B8, landed). -/
structure BridgePre (n : ℕ) (C : UCarriers n) : Prop where
  hdet : MovesS.DetHyp C.T C.RB C.hK
  hStateNe : HStateNe n C

/-! ## IB-F2 — the kernel pack (two layers; the area's honesty ledger) -/

/-- IB-F2 (above the line): the CONSTRUCTION-FEEDING rows — the open kernels
    the D-group constructions consume as arguments (file header, dependency
    order; NOT consumed by `mkUInstance`, whose binders already carry the
    constructions' outputs).
    * `transfer` — (†6) THE TRANSFER ROW (IB-D5's ratification-flagged
      structure): TREE-N's decision/realization stability across levels (the
      note's Thm 2.1 face).  OWNER: HC-2/D4R0K + TREE-N.  FENCED SIBLING:
      `MovesT.treeN_stable` (MovesT/E11_treeN.lean:90, a fenced sorry) — cited,
      NEVER consumed.  Consumers: IB-D8 (canonical_stable), IB-D15 (vt_real),
      IB-D16 (vt_surj), treeOf coherence.
    * `slice_finite` — ROW DELETED 2026-07-30 (the pre-authorized R6-probe
      consequence: "on probe success this row LEAVES the pack"; N3 gate-class
      execution, `BRIDGE_ADJUDICATIONS_2026-07-30.md` SYNTHESIS PASS 1).  The
      BridgeD13 pigeonhole probe LANDED: (†9) CL-7's finiteness at the
      instance is now the PROVED theorem `bridge_slice_finite` below (from
      `realizedSelf_slice_finite`, whose own footprint is Lean-core; see the
      theorem's footprint disclosure), no longer an open kernel; only
      `slice_bound` (the p-uniformity claim, OWNER [4]/TRACK-COUNT) survives
      below the line.  Consumer unchanged: IB-D14 (`bridgeFibers`'s thrSlice
      argument) now takes the theorem.
    Parametric in the (†3) dictionary `boxeq` per header resolution 3 (wired at
    `Tpin.boxeq` = IB-A11's `boxEquivD`). -/
structure BridgeKernelsCtor (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N)) : Prop where
  transfer : TransferRow n p boxeq

/-- THE FORMER `slice_finite` ROW, PROVED (R6 probe success, 2026-07-30 — see
    the `BridgeKernelsCtor` docstring): every threshold slice of the σ-typed
    self-realized tree family (IB-D3/D4's carrier) is finite.  Derived from
    BridgeD13's `realizedSelf_slice_finite` (the carrier-free pigeonhole
    theorem at the pinned `bridgeTm`/`bridgeChart`) by injecting the carrier
    subtype along `Subtype.val` — the "subtype repackaging D14 performs"
    anticipated by the probe's header.  Supplies IB-D14's `slice_finite`
    argument at the final wiring (BridgeMk, intended-wiring display).
    FOOTPRINT DISCLOSURE (2026-07-30 `#print axioms`): the PROOF is Lean-core
    (both BridgeD13 probe theorems check at [propext, Classical.choice,
    Quot.sound]); this theorem's own footprint additionally shows `sorryAx`
    ONLY because its STATEMENT's carrier `bridgeTree`/`bridgeThr` names the
    IB-D1 designer data-sorries `bridgePol`/`bridgeTm` (R7, the scheduled
    designer round) — the same vocabulary conditionality every D-group object
    at the pinned models carries, not a proof gap. -/
theorem bridge_slice_finite (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (N : ℕ) : {T : bridgeTree n p σ | bridgeThr n p σ T ≤ N}.Finite := by
  have hval : Set.InjOn (fun T : bridgeTree n p σ => T.1)
      {T : bridgeTree n p σ | bridgeThr n p σ T ≤ N} :=
    fun T _ T' _ h => Subtype.ext h
  refine Set.Finite.of_finite_image ?_ hval
  refine Set.Finite.subset
    (realizedSelf_slice_finite (fun N' => bridgeTm p n N')
      (fun N' hN' => bridgeChart n N' hN') N) ?_
  rintro V ⟨T, hT, rfl⟩
  exact ⟨hT, T.2.2⟩

/-- IB-F2 (below the line): `BridgeKernels` — THE LEDGER ROWS over the
    constructed objects (bound as parameters per header resolution 1): the
    per-prime open kernels `mkUInstance` consumes beyond `BridgePre` and the
    constructions themselves.  EVERY field is a named open kernel of the MOVES
    note (§U-SQUEEZE, frozen 2026-07-24: ledger display 13224–13361), typed
    over built vocabulary, none True-instantiable (G2).  Everything NOT here
    and not inside a binder's own laws is PROVED outright by the area's units.
    The remaining §3.7 rows live per the file-header dependency order:
    `transfer` in `BridgeKernelsCtor` (construction side; `slice_finite` left
    the pack 2026-07-30 — R6 probe success, now `bridge_slice_finite` PROVED),
    `count_tie` as the assembled seam's third field (visible in the `seam`
    binder; Q7: named row, discharge chain D20/D21 off the default path). -/
structure BridgeKernels (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (p : ℕ) (hp : p.Prime)
    (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (seam : TreeSeam n p X F) (Tpin : @TreePin n p ⟨hp⟩ X F seam) : Prop where
  /-- CL-7's CONCLUSION FORM at the p-UNIFORM bound (round-2 CRITICAL 6): the
      decided-family slice cardinality is bounded by `K7.Tbound N` — ONE
      T(n, N) serving EVERY prime simultaneously.  `UInstance.cl7_slice`'s
      exact supply (wired by IB-F6).  NOTE DISPLAY: SQ.0/TRACK-COUNT (MOVES
      12925–13018).  OWNER: [4]; TRACK-COUNT is permanently fenced, so this
      row is carried, never discharged this campaign. -/
  slice_bound : ∀ (σ : SplittingType n) (N : ℕ),
    (F.thrSlice σ N).card ≤ K7.Tbound N
  /-- THE [3t] SOLVE-SIDE SEAM (`SolveSeam.series_tie`'s row, DefsLedger.lean:
      573): the tree-fiber series sum IS the chain's measured per-σ value —
      Haar mass of the canonical fibers vs the measured chain.  The note's
      named open premise; OWNER: [3t].  Consumer: IB-C5's `bridgeSolveSeam`
      (its `hseries` binder) inside IB-F3's ledger assembly. -/
  series_tie : ∀ σ : SplittingType n,
    F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
  /-- CL-4's OPERATIVE TRACE (`CapstoneLedger.cl4_env_tendsto`'s supply): the
      undecided envelope vanishes.  This is hExhaust AT GENERAL n — FENCED
      MATH (notes/UNIFORMITY_COMPLETION_BLUEPRINT_2026-07-30.md); the n = 2
      discharge candidate is the OM `hExhaustP` through the D19 agreement seam
      (IB-F7, OPTIONAL, off the default path). -/
  env_tendsto : Tendsto X.env atTop (𝓝 0)
  /-- CL-10's VP + VP-SOUND citation duty (`CapstoneLedger.cl10_vpsound`'s
      supply; U10 clause (ii)'s engine through U11): every decided-σ class has
      true type σ.  OWNER: CL-10/[1] (VP) — open; the identification kernel of
      Architecture B (†8 tail). -/
  vp_sound : VPSound X
  /-- CL-10's (SIB)/(JC-multi) ROWS AT THE PINNED INSTANCE (`UInstance.sibjc`'s
      supply): exactly the hypothesis rows `MovesT.treeN` consumes at
      `Tpin.Tm N`/`Tpin.chart N` (DefsLedger.lean:389).  OWNER: HC-2 (the
      CL-10 kernels). -/
  sibjc : @SibJcRows n p ⟨hp⟩ X F seam Tpin
  /-- CL-6, TYPED (`CapstoneLedger.cl6`'s supply): the (iv)-POLY value+degree
      law package over the real carriers.  Q6 ADJUDICATED: kept a kernel row;
      if the S-area proves it at the real pack, the row moves out. -/
  cl6 : Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)
  /-- CL-11's (K-SUB) m = 1 classification OVER THE REAL ROSTER
      (`CapstoneLedger.cl11_ksub`'s supply).  Q6 ADJUDICATED: kept a row
      (a finite roster check at the n = 2 real pack may discharge it there). -/
  cl11_ksub : KsubM1C1T C.T
  /-- CL-17's PRODUCTION BURDEN (`CapstoneLedger.cl17`'s supply): W17ii at the
      chain's own carriers — the chain's OPEN projection, open BY DESIGN
      (never instance-suppliable data). -/
  cl17 : C.chain.wsh17_pin
  /-- CL-19's REPRESENTATIVE-INVARIANCE FACE (`CapstoneLedger.cl19_rep`'s
      supply, verbatim its field type): per-cell conditional mass is one
      function of the retained state.  OWNER: [2b]; the history/h_ent
      complement is U10's explicit `jcInvHist` parameter (slot IB-G10). -/
  cl19_rep : ∀ e (τ : C.T.State e) (x x' : C.MS.Rep e τ) (c : C.MS.Cell e τ)
    (q₀ : ℚ), q₀ ∈ C.MS.Pools → C.MS.activeState q₀ e τ →
    C.MS.μcell e τ x c q₀ = C.MS.μcell e τ x' c q₀

/-! ## IB-F6 — the cl7_slice wiring -/

/-- IB-F6: the `slice_bound` row supplies `UInstance.cl7_slice`'s exact field
    shape (DefsLedger.lean:842) — the p-UNIFORM decided-family bound at the
    constructed fiber series.  Deps: F2.  PROOF SKETCH (R, ~5): projection
    (`BK.slice_bound`); kept as its own unit so the pack-row → instance-field
    keying is a named, auditable step (consumed by IB-F4's `UInstance`
    literal). -/
theorem bridge_cl7_slice (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (p : ℕ) (hp : p.Prime)
    (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (seam : TreeSeam n p X F) (Tpin : @TreePin n p ⟨hp⟩ X F seam)
    (BK : BridgeKernels n C KC K7 p hp X F seam Tpin) :
    ∀ (σ : SplittingType n) (N : ℕ),
      (F.thrSlice σ N).card ≤ K7.Tbound N := sorry

end LeanUrat.MovesU
