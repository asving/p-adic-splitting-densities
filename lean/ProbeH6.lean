/- H6 DISCHARGE BLUEPRINT COMPILE PROBE (not a landing unit; deleted after probing).
   Every declaration below is a CANDIDATE verbatim statement for HDISCHARGE_H6.md.
   Probe discipline: BP_VI/BP_IV lesson — no statement enters the blueprint unprobed. -/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU2t
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.MovesU.DefsLedger
import LeanUrat.MovesT.V9_irrSat
import LeanUrat.Scaffold.ValueSide.Hyps
import LeanUrat.Scaffold.DictIII.CU1
import LeanUrat.HC2.Defs

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII
open LeanUrat.MovesU
open scoped ENNReal

-- Probe 0: the corpus quarry names elaborate as expected.
#check @MovesT.IrrHalts
#check @MovesT.irrVerdictOf
#check @MovesT.accE
#check @MovesT.irr_iff_mu_one
#check @LeanUrat.Scaffold.DictIII.machineProj
#check @LeanUrat.Scaffold.ValueSide.AssembledPack
#check @LeanUrat.MovesJ.ReadsOf

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- (H6-A1a) E-side accumulated ramification over the seam continuing part 𝐇°:
    eAccE = ∏ eᵢ (empty product 1 at k′ = 0 — matches (accE₀, accF₀) = (1, f₀)). -/
def eAccE (H : EHist p F) : ℕ := (H.nodes.map fun ν => ν.e).prod

/-- (H6-A1b) E-side accumulated residue degree: f₀ · ∏ gᵢ (the sel-selected g's). -/
def eAccF (H : EHist p F) : ℕ :=
  H.psi0.natDegree * (H.nodes.map fun ν => (ν.sel.elim 1 Prod.fst)).prod

/-- (H6-A2a) Seam decidedness, τ-irr branch (repaired: LAST read saturated,
    any read count k′ ≥ 1; CUC §9.2 DEC(τ-irr)). H is 𝐇° — all nodes continuing. -/
def DecIrrSeam (H : EHist p F) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g, ν.sel = some (g, 1))

/-- (H6-A2b) Seam decidedness, τ-hen branch (repaired: keyed at THE GIVEN read D,
    not ∃-over-lawless data; k′ = 0; CUC §9.2 DEC(τ-hen)). -/
def DecHenSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes = [] ∧
    (H.a0 = 1 ∨ ∃ S ∈ D.principalSides 0, S.isNegInfty = true)

/-- (H6-A2c) DEC = τ-irr ∨ τ-hen. -/
def DecSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  DecIrrSeam H ∨ DecHenSeam f H D

/-- (H6-A3) The deep exact-key corner (CUC §9.4 (T-DEC-cor)): k′ ≥ 1,
    μ_{k′} ≥ 2, and the slope-−∞ (j₀ = 1) side at the level-(k′+1) read. -/
def DeepCorner (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g μ, ν.sel = some (g, μ) ∧ 2 ≤ μ) ∧
    ∃ S ∈ D.principalSides H.nodes.length, S.isNegInfty = true

/-- (H6-A4a) The forced terminal datum, repaired: keyed at the GMN read D
    (slope = the unique level-(k′+1) principal side; CUC §9.2 — a function of
    (f, c), NEVER of the emitted record). -/
structure TerminalDatumD where
  slope : Option (ℕ × ℕ)
  verdict : ℕ × ℕ

open scoped Classical in
/-- (H6-A4b) terminalDatumD: slope from the (forced-unique) head side; verdict
    (eAccE, eAccF) on DecIrrSeam, (1, f₀) on the Hensel branch. -/
noncomputable def terminalDatumD (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : TerminalDatumD :=
  { slope := (D.principalSides H.nodes.length).head?.bind fun S =>
      if S.isNegInfty then none else some (S.e, S.h)
    verdict := if DecIrrSeam H then (eAccE H, eAccF H) else (1, H.psi0.natDegree) }

/-- (H6-A5) Definition RC, repaired ((RC-read) against a side of the level-(k′+1)
    read; (RC-verd) against the record function). Non-circular: D is polygon data
    of f over Θ(𝐇°); no field mentions the true factor. -/
def RCConsistentD (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (ν : ENodeData) (EF : ℕ × ℕ) : Prop :=
  ν.sel = none ∧
  (∃ S ∈ D.principalSides H.nodes.length,
    (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u)) ∧
  EF = (terminalDatumD f H D).verdict

/-- (H6-A6) The terminal-emission interface: the engine's verdict-carrying
    emission relation presented at the E-side carriers. reaches f H = a complete
    run on f whose continuing part dresses to 𝐇° = H; emits f H ν EF = it emits
    terminal record ν announcing pair EF there. -/
structure TerminalEmission (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] where
  reaches : Polynomial ℤ_[p] → EHist p F → Prop
  emits : Polynomial ℤ_[p] → EHist p F → ENodeData → (ℕ × ℕ) → Prop
  emits_terminal : ∀ f H ν EF, emits f H ν EF → ν.sel = none
  emits_reaches : ∀ f H ν EF, emits f H ν EF → reaches f H
  reaches_continuing : ∀ f H, reaches f H → ∀ ν ∈ H.nodes, ν.sel ≠ none

/-- (H6-A7) THE (H6) TERMINAL-SEAM ROW TRIO, repaired (CUC §9.4 at R4's grading),
    quantified at an emission interface E. Field ↔ row: tDECdec = (T-DEC-dec)
    emission discipline (the engine BOOKS at decided sites), tDECcor = the corner
    fence (verdict-carrying emissions live at DEC ∨ corner ONLY), tREAD = (RC-read)
    supply, tVERD = (RC-verd) supply. -/
structure TerminalSeamHypsE (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop where
  tDECdec : ∀ f H (D : GMNData f (Theta H)),
    E.reaches f H → (DecIrrSeam H ∨ (DecHenSeam f H D ∧ 2 ≤ H.a0)) →
    ∃ ν EF, E.emits f H ν EF
  tDECcor : ∀ f H ν EF (D : GMNData f (Theta H)),
    E.emits f H ν EF → DecSeam f H D ∨ DeepCorner f H D
  tREAD : ∀ f H ν EF (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
    E.emits f H ν EF → DecSeam f H D → ConsF f H D R →
    ∃ S ∈ D.principalSides H.nodes.length,
      (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u)
  tVERD : ∀ f H ν EF (D : GMNData f (Theta H)),
    E.emits f H ν EF → DecSeam f H D →
    EF = (terminalDatumD f H D).verdict

/-- (H6-A8) Engine-tie (canonicity): E presents the AS-BUILT engine — reaches
    factors through coherent machine histories realizing f (machineProj), and
    emitted verdicts are the machine's announced record-function values at
    IrrHalts leaves. The SHAPE-field supply is deliberately NOT tied here — the
    machine-side home of (T-READ) is purely owed (CUC §9.4); unit C0 builds it. -/
structure EngineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop where
  reaches_engine : ∀ f H, E.reaches f H →
    ∃ (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M),
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineProj M hM).val.continuingPart = H
  emits_irr_verdict : ∀ f H ν EF, E.emits f H ν EF → DecIrrSeam H →
    ∃ (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M),
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineProj M hM).val.continuingPart = H ∧
      MovesT.IrrHalts M ∧
      EF = (MovesT.accE M, MovesT.accF M)

/-- (H6-A9) THE K4-FACING ROW (unblocks BP_IV S5b/D4): the (H6) trio at every
    engine-tied emission, keyed at the consumption site (X, FF). -/
structure TerminalSeamRows (n p : ℕ) [Fact p.Prime] (X : ClassifierSpec n p)
    (FF : FiberSeries n p X) : Prop where
  seam : ∀ (F' : Type) [Field F'] [Finite F'] (E : TerminalEmission p F'),
    EngineTied n p F' E → TerminalSeamHypsE p F' E

/-- (H6-A10) D-11 widened-charge item (vii): the six H.6 fences as one displayed
    conformance row over the assembled pack — general-n in-fence conformance of
    the BUILT tables (V-n3 178/178 + H-n3 151/151 are the sealed n = 3 evidence,
    flags not proofs). Fence kernels themselves stay [2b]-parked perimeter. -/
structure FenceVII (n : ℕ) (P : LeanUrat.Scaffold.ValueSide.AssembledPack n) where
  xhdDEx : Prop
  m4bTAud : Prop
  urCount : Prop
  xhdUX : Prop
  hListGen : Prop
  ePos : Prop
  inFence : xhdDEx ∧ m4bTAud ∧ urCount ∧ xhdUX ∧ hListGen ∧ ePos

-- Probe A11: the S5b-shaped binder context elaborates with TerminalSeamRows.
example {n p m : ℕ} [Fact p.Prime]
    {C : UCarriers n} {X : ClassifierSpec n p} {FF : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (seam : TreeSeam n p X FF)
    (K4 : TerminalSeamRows n p X FF) : True := trivial

end LeanUrat.Scaffold.HDischarge.H6
