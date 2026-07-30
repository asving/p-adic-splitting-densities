/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeKernels
import LeanUrat.MovesU.BridgeSolve
import LeanUrat.MovesU.U10_theoremU

/-!
# BP1 group F — the assembly + the firing theorem (IB-F3, IB-F4, IB-F5)

E-phase skeletons per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §1 (G3) /
§3.7 assembly displays / §4 group F, cluster BP1-c10.  File name per the
blueprint's §4 prescription ("BridgeKernels.lean + BridgeMk.lean (F)").
Units in this file:

* (device) `BridgeInputs` — the per-prime constructed-object bundle (see the
  transcription resolution below; NOT a unit, NOT an achievement).
* IB-F3  `bridgeCapstoneLedger` (+ its seam rfl-display) — the `CapstoneLedger`
         assembly from the pack rows + the constructed seam + the checksum.
* IB-F4  `mkUInstance` — G3's per-prime instance constructor: conclusion
         VERBATIM the blueprint's, `UInstance n C KC K7 (bridgeSolve C BP.hdet)
         p hp` (IB-C1's `bridgeSolve` landed — no surrogate solve).
* IB-F5  `theoremU_fired` — Theorem U fired at the constructed instance family;
         conclusion verbatim `theoremU`'s (U10_theoremU.lean:104) at
         S := `bridgeSolve C BP.hdet` and inst := `fun p hp => mkUInstance …`.

## TRANSCRIPTION RESOLUTION (recorded per the E-phase rules)

G3 types `mkUInstance` over the pack alone because in the blueprint's
dependent-record architecture the constructions happen INSIDE the pack/the
constructor.  The construction units live in concurrently-writing sibling
clusters and are themselves PARAMETRIC with the wiring deferred to THIS unit
(BridgeD11/D14/D17/D18 headers: "IB-F4 instantiates") — so at E-phase the
constructed per-prime objects enter as ONE recorded binder bundle,
`BridgeInputs`, and the intended final wiring is FIXED here (each field's
supplier named below).  `BridgeInputs` is a TRANSCRIPTION DEVICE: it must NOT
survive as a permanent hypothesis surface — the post-prover wiring pass
supplies it FROM the landed constructions, and the campaign's conditionality
claim of record is G3's: the p-uniform packs (other areas) + the
`BridgePre`/`BridgeKernels`(+Ctor) rows + the seam-carried count_tie + the
thirteen slots + per-p (REG-p).

INTENDED FINAL WIRING (the suppliers, per the landed sibling units):
* `X`      := `bridgeClassifierSpec n p (bridgeCanonical …) (canonical_stable
              from IB-D8 at the Ctor transfer row) (bridgeZfType)` (IB-D11 at
              IB-D7/D8/E11); `hXbase` := rfl (D11's `baseSection :=
              .teichmuller`, display `bridgeClassifierSpec_teichmuller`).
* `F`      := `bridgeFibers n p X (bridgeTree n p) (bridgeMass-composite)
              (bridgeThr n p) Ctor.slice_finite` (IB-D14 at IB-D3/D4/D12/D13).
* `seam`   := `⟨bridgeTreeOf …, bridgeTreeOf_thr_le …, count_tie⟩` (IB-D17's
              treeOf/thr_le + the [3t] count_tie row as the THIRD FIELD — the
              open kernel rides the seam VISIBLY, per BridgeKernels.lean's
              dependency-order record; Q7: named row).
* `Tpin`   := `bridgeTreePin n p X F seam bridgePol bridgeTm boxEquivD …`
              (IB-D18 at IB-D1/D2/A11/D4/D15/D16/D7/D17).
* `D`      := `bridgeRegData hn C BP.hStateNe p` (IB-B8, landed);
  `Dpin`   := IB-B10's `bridgeRegPin` (B-cluster, with B5/B6/B11–B13).
* `bridge` := IB-E9's `bridgeZpBridge` assembly (Q2-GATED: zf_pos/zf_factor
              provers E5–E7 run only after the IB-E0-conditional ramIdx/resDeg
              repair — BRIDGE_ADJUDICATIONS Q2; a stall on any ZpBridge law is
              an orchestrator adjudication, never a catch-all row).
* `BK`     := the nine ledger rows of `BridgeKernels` (IB-F2) at the above.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- THE PER-PRIME CONSTRUCTED-OBJECT BUNDLE (transcription device — file
    header; every field's intended supplier is named there).  Fields = exactly
    the constructed per-prime objects `UInstance` needs MINUS the ledger `L`
    (IB-F3 rebuilds `L` from the pack rows — that replacement IS `mkUInstance`'s
    content), PLUS the two definitional pins the constructions make `rfl`
    (`hXbase`) and the kernel pack `BK` over the bundle.  The [3t] count_tie
    row is the `seam` field's own third field (visible, open). -/
structure BridgeInputs (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (p : ℕ) (hp : p.Prime) where
  X : ClassifierSpec n p
  /-- rfl at IB-D11's construction (`bridgeClassifierSpec_teichmuller`);
      supplies `CapstoneLedger.o3_teichmuller`. -/
  hXbase : X.baseSection = BaseSection.teichmuller
  F : FiberSeries n p X
  seam : TreeSeam n p X F
  Tpin : @TreePin n p ⟨hp⟩ X F seam
  D : RegData p
  Dpin : RegPin C D
  bridge : @ZpBridge n p ⟨hp⟩ X
  BK : BridgeKernels n C KC K7 p hp X F seam Tpin

/-! ## IB-F3 — the CapstoneLedger assembly -/

/-- IB-F3: `bridgeCapstoneLedger` — the per-p typed ledger ASSEMBLED from the
    kernel pack + the constructed seam + the landed checksum, at THE solve
    family `bridgeSolve C BP.hdet` (IB-C1, landed).  Deps: C4, C5, D14, D17
    (through `BD`), F2.  PROOF SKETCH (§3.7 display; R, ~20 — record literal):
    `cl4_env_tendsto := BD.BK.env_tendsto`; `cl6 := BD.BK.cl6`;
    `cl10_vpsound := BD.BK.vp_sound`; `cl11_ksub := BD.BK.cl11_ksub`;
    `cl17 := BD.BK.cl17`; `cl19_rep := BD.BK.cl19_rep`;
    `o3_teichmuller := BD.hXbase`; `seam := BD.seam`;
    `ssrc := bridgeSolveSeam C BD.F BP.hdet BD.BK.series_tie` (IB-C5 —
    equivalently ⟨series_tie, fun _ _ => rfl⟩, r_is_solve rfl by definitional
    proof irrelevance of the `DetHyp` binder);
    `rs4_checksum := rs4_checksum_bridge C BP.hdet` (IB-C4, †10b). -/
noncomputable def bridgeCapstoneLedger (n : ℕ) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (BP : BridgePre n C)
    (p : ℕ) (hp : p.Prime) (BD : BridgeInputs n C KC K7 p hp) :
    CapstoneLedger n p C BD.X BD.F (bridgeSolve C BP.hdet) BD.D := sorry

/-- IB-F3 (seam display): the assembled ledger's seam IS the bundle's seam —
    `rfl` once the record literal lands (the assembly pins `seam := BD.seam`);
    consumed by IB-F4's `Tpin`/`sibjc` wiring (their types are keyed to
    `L.seam`, `UInstance` fields Tpin/sibjc, DefsLedger.lean:840–841). -/
theorem bridgeCapstoneLedger_seam (n : ℕ) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (BP : BridgePre n C)
    (p : ℕ) (hp : p.Prime) (BD : BridgeInputs n C KC K7 p hp) :
    (bridgeCapstoneLedger n C KC K7 BP p hp BD).seam = BD.seam := sorry

/-! ## IB-F4 — the per-prime instance constructor (G3) -/

/-- IB-F4: `mkUInstance` (G3) — for every prime, the genuine (non-surrogate)
    `UInstance` at THE solve family `bridgeSolve C BP.hdet` (conclusion
    VERBATIM the blueprint's G3 display).  The constructed per-prime objects
    enter through `BD` (file-header transcription resolution; suppliers named
    there); `hn` is G3's fidelity binder (feeds `bridgeRegData`'s `instNe` at
    the final wiring — blueprint REVISION 2 finding 2).  Deps: ALL construction
    units + F2 + F3 + F6.  PROOF SKETCH (R, ~20 — record literal):
    `X := BD.X; F := BD.F; D := BD.D;
     L := bridgeCapstoneLedger … BD (IB-F3); Dpin := BD.Dpin;
     bridge := BD.bridge; Tpin := BD.Tpin (transported along
     bridgeCapstoneLedger_seam); sibjc := BD.BK.sibjc (same transport);
     cl7_slice := bridge_cl7_slice … BD.BK (IB-F6)`. -/
noncomputable def mkUInstance (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (BP : BridgePre n C)
    (p : ℕ) (hp : p.Prime) (BD : BridgeInputs n C KC K7 p hp) :
    UInstance n C KC K7 (bridgeSolve C BP.hdet) p hp := sorry

/-! ## IB-F5 — Theorem U, fired -/

/-- IB-F5: `theoremU_fired` — Theorem U at the constructed instance family:
    apply `theoremU` (U10_theoremU.lean:104) at (C, KC, K7,
    S := `bridgeSolve C BP.hdet`, KT, the 13 slot parameters, inst :=
    `fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp)`).  CONCLUSION
    VERBATIM `theoremU`'s at those values (G3).  Deps: F4.

    HONEST CONDITIONALITY OF RECORD (G3's list, restated): the p-uniform packs
    (`KC`/`K7`/`KT` — sibling areas), `BridgePre`'s two ratified named premises,
    the `BridgeKernelsCtor` + `BridgeKernels` rows and the seam-carried
    count_tie (each a named open kernel, inside `BD` at E-phase — the
    file-header device record), the THIRTEEN reserved slot parameters (wave-4
    boundary, True-instantiable pending wave-D — U10's docstring record; the
    G-group `theoremU_bridged` consumption is IB-G13, another cluster), and
    per-p (REG-p) — at a p failing (REG-p): NO CLAIM (D8).  Never describe
    this theorem as unconditional. -/
theorem theoremU_fired (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (KT : UpstreamTyped n KC)
    (BP : BridgePre n C)
    (rel1 rel2a rel2b rel2d rel2e rel3 : Prop)
    (rs0Lump trackRule dnLattice : Prop)
    (m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) (hrel2a : rel2a) (hrel2b : rel2b) (hrel2d : rel2d)
    (hrel2e : rel2e) (hrel3 : rel3)
    (hrs0 : rs0Lump) (htrk : trackRule) (hdn : dnLattice)
    (hm15 : m1m5Echo) (hx1a : x1aDict) (hm4b : m4bConst) (hjc : jcInvHist)
    (BD : ∀ (p : ℕ) (hp : p.Prime), BridgeInputs n C KC K7 p hp) :
    ∃ R : SplittingType n → RatFunc ℚ,
      R = (bridgeSolve C BP.hdet).R ∧
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime),
        RegP (mkUInstance n hn C KC K7 BP p hp (BD p hp)).D →
          -- (U-n): the exported two-sided bracket
          (∀ (σ : SplittingType n) (N : ℕ),
            (evalℝ ⟨R⟩ σ p
                - (mkUInstance n hn C KC K7 BP p hp (BD p hp)).X.env N)
                  * (p : ℝ) ^ (n * N)
                ≤ ((mkUInstance n hn C KC K7 BP p hp (BD p hp)).X.decided σ N : ℝ) ∧
              ((mkUInstance n hn C KC K7 BP p hp (BD p hp)).X.decided σ N : ℝ)
                ≤ evalℝ ⟨R⟩ σ p * (p : ℝ) ^ (n * N))
          -- (i) the classifier-keyed density
          ∧ (∀ σ : SplittingType n,
            Tendsto ((mkUInstance n hn C KC K7 BP p hp (BD p hp)).X.dmass σ)
              atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
          -- (ii) the identification corollary
          ∧ (∀ σ : SplittingType n,
            Tendsto ((mkUInstance n hn C KC K7 BP p hp (BD p hp)).X.trueDmass σ)
              atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
          -- (ii-ℤ_p) the SAME limit for the ℤ_p-READ density
          ∧ (∀ σ : SplittingType n,
            Tendsto (@ZpBridge.zpDmass n p ⟨hp⟩ _
                (mkUInstance n hn C KC K7 BP p hp (BD p hp)).bridge σ)
              atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
          -- (iii) the undecided complement has mass 0
          ∧ Tendsto (mkUInstance n hn C KC K7 BP p hp (BD p hp)).X.env
              atTop (𝓝 0) := sorry

end LeanUrat.MovesU
