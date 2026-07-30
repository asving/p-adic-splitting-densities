/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.MovesC.Defs

/-!
# IB-G1 — the CInterface CARRIER SKELETON for the REL slot family (bridge BP1, §3.8)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 + §4 group G
(IB-G1: "CInterface-carrier skeleton for the REL family (from the parked MovesR
draft; statement-only). ADJ") and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
(BP1 Q5: "proceed now, statement-only, Codex audit before consumers").

RAW MATERIAL (the parked draft): `lean/notes/MOVESR_LEAN_BLUEPRINT_2026-07-28.md`
(rev 4) §D4's CInterface layers — `GradedCarrier` (D4(a)), `TowerData` + laws,
`BoxVol`, `REL1Counting`, `ReBased` (+ the FF2 `count` repair) — together with the
BUILT `MovesRBase.SpeciesSyntax`/`AlphabetData` (MovesRBase/Defs.lean:73/89).  The
MovesR corpus is PARKED (campaign ledger 2026-07-28: Codex final REJECT 15/2 — "the
CInterface SHAPE is right but faithfully TYPING the eleven §C statements needs the
full §C carrier vocabulary"; FABLE leg REJECT 3/4 — "carrier fields note-supported;
criticals LOCAL to the LST/TYP typings").  Accordingly THIS UNIT TRANSCRIBES THE
CARRIER LAYER ONLY; the eleven §C statement defs + `CStatements` (the layer the
audits refuted as typed) are NOT transcribed — re-typing them per the wave-5
resumption charge is exactly IB-G2/IB-G3's H-phase deliverable, over this carrier.

DEPS: — (raw material only; nothing here imports the bridge construction path).
CONSUMERS: IB-G2 (`Slot_rel1`, `Slot_rel2a/b/d/e`), IB-G3 (`Slot_rel3`),
IB-G11a (falsifiers), IB-G12 (closure manifest), IB-G13 (`theoremU_bridged`).

E-PHASE RESOLUTIONS (each a minimal ambiguity resolution, recorded per the
statement-writer charge; all flagged for the Q5 Codex audit):
* R-1 (naming): the draft's carrier bundle `MovesR.ReBased p Sp AD δ n` lands here
  as `CInterface p Sp AD δ n` — the BP1 blueprint's own name for G1's carrier
  ("the CInterface-RELATIVE typed Prop `Slot_rel3 (CI : …)` over G1's carrier").
  All declarations re-homed into `LeanUrat.MovesU` (the MovesR corpus proper stays
  parked; MovesRBase re-homes nothing).
* R-2 (phantom indices): the draft writes `GradedCarrier p δ` but no field of
  `GradedCarrier` mentions `p` or `δ`; both are kept as EXPLICIT phantom parameters
  (indexing discipline — call sites in the draft demand them), with the unused
  `[Fact p.Prime]` dropped from `GradedCarrier` alone.
* R-3 (the F3-3 repair, resumption charge "link floorB to K.lines with a
  block-edge field + staircase equation"): the carrier GAINS the `blockEdge` field
  the recorded resumption charge demands, so the H-phase can state the staircase
  equation `floorB H b = (lines H (top read)).at (blockEdge H b)` as a LAW instead
  of leaving `floorB` a free field (the F3-3 defect).  `floorB`/`floorC` stay data
  here — the law is statement-layer content (IB-G2).
* R-4 (namespace qualification, per the draft's own SKELETON STATUS note):
  `DigitSystem` = `LeanUrat.Moves.DigitSystem` (Moves/DefsT.lean:187),
  `Line` = `LeanUrat.MovesC.Line` (MovesC/Defs.lean:255).

THE RECORDED TRAPS (documented here at the carrier, binding on IB-G2's H-phase —
the p^N-torsion lesson, campaign ledger MovesR FABLE leg + MOVESR_AUDIT_FABLE3):
* F3-1: the jet-additivity clause as the draft typed it (`jet H` a group hom
  `(O_δ^n, +) → (F_δ^{mOf}, +)`) is GROUP-THEORETICALLY IMPOSSIBLE for any genuine
  digit parameterization (O_δ/p^N has p^N-torsion; an additive map into an
  elementary abelian p-group factors through mod p) — the intended instance would
  FALSIFY REL.1.  The faithful additive object is the LEVEL-SET-DIGITS →
  GRADED-PIECE COMPOSITE `(y_c)_c ↦ inγ γ (slotCoeff H B y)` (MOVES 3801–07,
  9401–04), additive in the DIGIT tuple — expressible from the fields
  `ht`/`blkOf`/`slotCoeff`/`G.inγ` below; NO statement may assert additivity of
  `jet` on box points.
* F3-2: alphabets are priced on the slot-image SPAN in the graded piece (TYP(b)
  MOVES 3815–21; the F₉ a = 2 instance is the check), NEVER on the attainable
  digit-VALUE set `Set.range (jet H · i)`.
The worked δ = 1 instantiation pattern for all of this is `HC1/DefsCar.lean`
(`GradedCarrierR`/`typComposite`/`alphabet`/`floorB`-by-construction).

STATEMENT-FENCE FLAG: every structure below is NEW carrier vocabulary (raw
material transcription, not a built-corpus statement); ratification = the Q5
Codex audit gate before any consumer (IB-G13) lands.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-- **CInterface layer (a) — `GradedCarrier`** (parked draft D4(a), VERBATIM; the
shape is ratified in-repo at δ = 1 as `HC1.GradedCarrierR`, DefsCar.lean:124): the
D.3(e)/§C graded vocabulary as abstract types with laws; NO construction —
instantiation from the OM engine is HC-1's declared deliverable.  Fields:
coefficients, graded pieces, the K1-chain-weight function, the initial-form/class
map, and its laws (ultrametric weight, additivity at weight, kills-weight-above,
weight detection).  `p`/`δ` are phantom indices (E-phase resolution R-2). -/
structure GradedCarrier (p : ℕ) (δ : ℕ+) where
  Coeff : Type                             -- slot coefficients B
  [coeffAdd : AddCommGroup Coeff]
  Gr : ℚ → Type                            -- D.3(e)(i)'s graded pieces
  [grAdd : ∀ γ, AddCommGroup (Gr γ)]
  w : Coeff → WithTop ℚ                    -- the K1-chain-weight function
  inγ : (γ : ℚ) → Coeff → Gr γ             -- the initial-form / class map
  w_add : ∀ B B', min (w B) (w B') ≤ w (B + B')
  inγ_add : ∀ (γ : ℚ) (B B'), (γ : WithTop ℚ) ≤ w B → (γ : WithTop ℚ) ≤ w B' →
    inγ γ (B + B') = inγ γ B + inγ γ B'    -- additivity at weight γ
  inγ_kills : ∀ (γ : ℚ) B, (γ : WithTop ℚ) < w B → inγ γ B = 0  -- kills weight above
  inγ_detects : ∀ (γ : ℚ) B, w B = (γ : WithTop ℚ) → inγ γ B ≠ 0  -- weight detection

attribute [instance] GradedCarrier.coeffAdd GradedCarrier.grAdd

/-- (R0-tower) carrier (parked draft, verbatim): the re-based classifier tower of
one history — "built afresh, NOT by scalar-extending the ℤ_p tower".  Base shape
F₁ = F_δ[x]/(φ̄), climb F_{k+1} = F_k[z]/(ψ_k), residual factors OVER THE NEW BASE
(the polynomials live over the actual tower carriers).  Laws split §A / §B1 /
§B2-DEF for the ledger (the three Prop structures below). -/
structure TowerData (δ : ℕ+) where
  len : ℕ
  Res : Fin (len + 1) → Type              -- F₁, …, F_{len+1}
  [resField : ∀ k, Field (Res k)]
  baseEmbed : ↥(Fsub p δ) →+* Res 0
  stepEmbed : ∀ k : Fin len, Res k.castSucc →+* Res k.succ
  φbar : Polynomial ↥(Fsub p δ)           -- §A's φ̄, over F_δ
  ψ : ∀ k : Fin len, Polynomial (Res k.castSucc)  -- residual factors ψ_k over F_k

attribute [instance] TowerData.resField

/-- §A re-based, the typed base-shape laws: φ̄ monic irreducible OVER F_δ and
F₁ ≃ F_δ[x]/(φ̄) compatibly with the base embedding. -/
structure TowerData.BaseLaws {δ : ℕ+} (T : TowerData p δ) : Prop where
  monic : T.φbar.Monic
  irr : Irreducible T.φbar
  pres : ∃ e : T.Res 0 ≃+* AdjoinRoot T.φbar,
    ∀ x : ↥(Fsub p δ), e (T.baseEmbed x) = algebraMap _ _ x

/-- §B2-DEF (D.0) re-based, the typed climb laws: each ψ_k monic irreducible over
the ACTUAL stage field, each step the quotient presentation F_{k+1} = F_k[z]/(ψ_k). -/
structure TowerData.ClimbLaws {δ : ℕ+} (T : TowerData p δ) : Prop where
  monic : ∀ k, (T.ψ k).Monic
  irr : ∀ k, Irreducible (T.ψ k)
  pres : ∀ k, ∃ e : T.Res k.succ ≃+* AdjoinRoot (T.ψ k),
    ∀ x, e (T.stepEmbed k x) = AdjoinRoot.of (T.ψ k) x

/-- §B1 re-based, the typable residue ("the same construction run over the new
base"): finite stage carriers of characteristic p.  The graded internals
(gr_w(A), L, T) are (R0-tower)-fenced to REL.1's pass — recorded, not typed. -/
structure TowerData.StageCarrierLaws {δ : ℕ+} (T : TowerData p δ) : Prop where
  fin : ∀ k, Finite (T.Res k)
  charP : ∀ k, CharP (T.Res k) p

/-- The finitely-additive cylinder-pinned box volume over the degree-n coefficient
box on O_m (parked draft, verbatim): `vol_cyl` rules out dummy measures;
`events_level` (CF15) is the finitely-additive reading of "digit cylinders
generate" — every priced event is level-determined, so `vol` is FORCED to be the
normalized Haar mass.  Inhabitation story: the Haar construction of the REL.1
pass; no instance is built here. -/
structure BoxVol (m : ℕ+) (n : ℕ) where
  events : Set (Set (Fin n → ↥(O p m)))
  univ_mem : Set.univ ∈ events
  compl_mem : ∀ W ∈ events, Wᶜ ∈ events
  union_mem : ∀ W ∈ events, ∀ W' ∈ events, W ∪ W' ∈ events
  cyl_mem : ∀ (N : ℕ) (g : Fin n → ↥(O p m)), cyl p m N g ∈ events
  vol : Set (Fin n → ↥(O p m)) → ℚ
  vol_nonneg : ∀ W, 0 ≤ vol W
  vol_empty : vol ∅ = 0
  vol_univ : vol Set.univ = 1
  vol_add : ∀ W ∈ events, ∀ W' ∈ events,
    Disjoint W W' → vol (W ∪ W') = vol W + vol W'
  vol_cyl : ∀ (N : ℕ) (g : Fin n → ↥(O p m)),
    vol (cyl p m N g) = ((qq p m : ℚ) ^ (n * N))⁻¹
  events_level : ∀ W ∈ events, ∃ (N : ℕ) (G : Finset (Fin n → ↥(O p m))),
    W = ⋃ g ∈ G, cyl p m N g

/-- Counting interface for (REL.1-b) (parked draft, verbatim): fixed box degree n,
nonempty carriers, vols THROUGH the pinned `BoxVol`, loci indexed by their history.
NOTE (the draft's FF2): the display's LHS `#{f mod p^N ∈ S(H,Z)}` is NOT a field —
it is DEFINED (`CInterface.count` below) from the classifier locus and the
cylinder partition, so no instance can supply a count unrelated to any classifier. -/
structure REL1Counting (δ : ℕ+) (n : ℕ) where
  V : BoxVol p δ n                        -- vol_{O_δ}, cylinder-pinned
  Hist : Type                             -- re-based histories H
  histNe : Nonempty Hist
  Locus : Hist → Type                     -- digit loci Z in H's frame
  locusNe : ∀ H, Nonempty (Locus H)
  kIdx : Hist → ℕ                         -- k, top node index
  Nmin : (H : Hist) → Locus H → ℕ         -- N(H, Z)
  freshEvent : (H : Hist) → ℕ → Set (Fin n → ↥(O p δ))    -- E_fresh(ν_i)
  freshEvent_mem : ∀ H i, freshEvent H i ∈ V.events
  locusEvent : (H : Hist) → Locus H → Set (Fin n → ↥(O p δ))  -- Z as a box event
  locusEvent_mem : ∀ H Z, locusEvent H Z ∈ V.events

/-- **THE CInterface CARRIER** (the parked draft's `ReBased`, re-homed per E-phase
resolution R-1; the carrier the REL slot family `Slot_rel1`/`Slot_rel2a/b/d/e`/
`Slot_rel3` quantifies over — IB-G2/IB-G3): digit spaces are F_δ-valued (the
O_δ-digit ATOM), jets expand box points into digit coordinates (C.0's block
expansion over F_δ), towers per history, frames with transports, per-position
alphabet dimensions a_δ WIRED to (EQ-2)'s `AlphabetData` via `posOfDigit`/`aDim_eq`
(the draft's FF4), pin sets (CF9: pin STATUS a proper carrier, the pinned set
DEFINED from it), the (ZC) statistic, the base-free floor lines for DOM, the
graded-carrier attachment `G` (D4(a)), and the height/block/floor carriers Lemma
LST's legs consume (FF1) — PLUS the resumption-charge `blockEdge` field (E-phase
resolution R-3).  TRAPS F3-1/F3-2 (file header) BIND every statement over this
carrier: the additive object is the level-set-digits → graded-piece composite
through `slotCoeff`/`G.inγ`, never `jet`-additivity on box points; alphabets are
priced on the slot-image span, never `Set.range (jet H · i)`. -/
structure CInterface (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) where
  C : REL1Counting p δ n
  mOf : C.Hist → ℕ                        -- digit count of H's jet frame
  mOf_pos : ∀ H, 0 < mOf H
  jet : (H : C.Hist) → (Fin n → ↥(O p δ)) → (Fin (mOf H) → ↥(Fsub p δ))
  tower : C.Hist → TowerData p δ          -- (R0-tower), per history
  Frame : C.Hist → Type                   -- C.0.5's frames
  frameNe : ∀ H, Nonempty (Frame H)
  T : (H : C.Hist) → Frame H → Frame H →  -- the frame transports
      (Fin (mOf H) → ↥(Fsub p δ)) → (Fin (mOf H) → ↥(Fsub p δ))
  SHZ : (H : C.Hist) → C.Locus H → Set (Fin n → ↥(O p δ))   -- the classifier locus S(H,Z)
  SHZ_mem : ∀ H Z, SHZ H Z ∈ C.V.events
  digitLocus : (H : C.Hist) → C.Locus H → Moves.DigitSystem (mOf H) ↥(Fsub p δ)  -- Z as digit system
  aDim : (H : C.Hist) → Fin (mOf H) → ℕ   -- a_δ at each digit position ((EQ-2) def part)
  /-- (FF4) the (R0-ledger)↔(EQ-2) wiring: each digit position sits at an
  `AlphabetData` position class, and its per-digit exponent IS that class's a_δ. -/
  posOfDigit : (H : C.Hist) → Fin (mOf H) → AD.Pos
  aDim_eq : ∀ H i, aDim H i = AD.aDim δ (posOfDigit H i)
  /-- (CF9) PIN STATUS as a proper carrier, the pinned set DEFINED from it. -/
  Status : Type
  pinStatus : (H : C.Hist) → Frame H → C.Locus H → Fin (mOf H) → Status
  constrained : Status → Prop
  pinnedIn : (H : C.Hist) → Frame H → C.Locus H → Finset (Fin (mOf H))
  pinnedIn_spec : ∀ H F Z i, i ∈ pinnedIn H F Z ↔ constrained (pinStatus H F Z i)
  zcStat : (H : C.Hist) → Frame H → C.Locus H → ℤ            -- C.1.5's (ZC) statistic
  lines : (H : C.Hist) → ℕ → MovesC.Line  -- base-free floor lines (MovesC, D8)
  interiorEnd : C.Hist → ℕ
  /-- THE CInterface ATTACHMENT (D4(a)): the graded carrier this instance's REL
  statements quantify over. -/
  G : GradedCarrier p δ
  /-- LST carriers (FF1): absolute height, block assignment, floors, factor-interior
  blocks, the engine's floor downset, each coordinate's BASIS MONOMIAL in the
  carrier, and each block's SLOT COEFFICIENT at a digit vector (the engine's weight
  is `G.w (slotCoeff …)`, never a free field). -/
  ht : (H : C.Hist) → Fin (mOf H) → ℚ
  blkOf : (H : C.Hist) → Fin (mOf H) → ℕ
  /-- E-PHASE RESOLUTION R-3 (the resumption charge's block-edge map, the F3-3
  repair's carrier half): the block's left base edge in H's frame — the slot the
  staircase law (IB-G2's statement layer) evaluates `lines` at to PIN `floorB`. -/
  blockEdge : (H : C.Hist) → ℕ → ℕ
  floorC : (H : C.Hist) → Fin (mOf H) → ℚ
  floorB : (H : C.Hist) → ℕ → ℚ
  interiorB : (H : C.Hist) → ℕ → Prop
  floorSet : (H : C.Hist) → ℕ → Set (Fin (mOf H))
  mono : (H : C.Hist) → Fin (mOf H) → G.Coeff
  slotCoeff : (H : C.Hist) → ℕ → (Fin (mOf H) → ↥(Fsub p δ)) → G.Coeff
  /-- (CF8) the note's own interior anchor: constrained digits sit on
  factor-interior blocks, so `interiorB ≡ False` forces the degenerate all-free
  perimeter instead of silently discharging the LST legs. -/
  interior_fresh : ∀ H (F : Frame H) Z, ∀ i ∈ pinnedIn H F Z, interiorB H (blkOf H i)

/-- `#{ f mod p^N ∈ S(H, Z) }` — the (REL.1-b) LHS, DEFINED from in-corpus
vocabulary (the draft's FF2 repair, verbatim — kills the free-count instances):
the number of level-N cylinder classes meeting the classifier locus.  For
N ≥ N(H,Z) these are exactly the level-N residue points of S(H,Z). -/
noncomputable def CInterface.count {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {δ : ℕ+} {n : ℕ} (K : CInterface p Sp AD δ n)
    (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ) : ℕ :=
  Nat.card {W : Set (Fin n → ↥(O p δ)) // ∃ f ∈ K.SHZ H Z, W = cyl p δ N f}

end LeanUrat.MovesU
