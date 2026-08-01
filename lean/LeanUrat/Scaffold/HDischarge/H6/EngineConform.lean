/-
HDISCHARGE_H6 §4 Wave B — `H6/EngineConform.lean`: unit B0 (EASY, statement-only).
Statement transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 B0.

Engine-tie canonicity: what "the engine's emission" means — every reached seam
and every emitted irr verdict is realized by a coherent machine history M that
is a classifier run on f (`MovesJ.ReadsOf`) whose projected 𝔈-history's
continuing part is the seam. Deliberately does NOT tie ν's shape fields —
(T-READ)'s machine home is owed (blueprint §3.3(a)); the C0 upgrade is where
tREAD becomes provable.

FOOTPRINT RULE (blueprint §4 B0): binds `machineEHist` (CU1's certificate-free
projected value, = `machineProj_val`), NOT `machineProj` — the latter bundles
the `EWF` certificate whose W3 row is CU1's one recorded honest sorry, so any
statement binding it would inherit `sorryAx`. Coherence rides as the explicit
`MovesC.HistoryCoherent M` conjunct instead.

Deps: A2 (`DecIrrSeam`), A6 (`TerminalEmission`) in `H6/Emission.lean`;
corpus `machineEHist` (DictIII/CU1), `MovesJ.ReadsOf` (HC2/Defs),
`MovesT.IrrHalts`/`accE`/`accF` (MovesT/Defs).
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU1
import LeanUrat.Scaffold.DictIII.O2aOrder1
import LeanUrat.Scaffold.HDischarge.H6.Emission
import LeanUrat.HC2.U31_gateReadsOf

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII

/-- H6-B0 (VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit B0):
engine-tie canonicity. `reaches_engine`: every reached seam is the continuing
part of a coherent, `ReadsOf`-lawful machine history's projection.
`emits_irr_verdict`: every emitted verdict pair at a decided irr seam is THE
machine accumulator pair `(accE M, accF M)` of an `IrrHalts` run realizing the
seam. Shape fields of ν are NOT tied here (§3.3(a) — owed at C0). -/
structure EngineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop where
  reaches_engine : ∀ f H, E.reaches f H →
    ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H
  emits_irr_verdict : ∀ f H ν EF, E.emits f H ν EF → DecIrrSeam H →
    ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H ∧
      MovesT.IrrHalts M ∧
      EF = (MovesT.accE M, MovesT.accF M)

/-! ## Unit B1 — the canonical site/verdict emission `engineEmissionSV`

Relational body transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4
unit B1 (the EXACT displayed body — fold round 1, Codex finding 10: probe
GREEN). The four interface laws are proved below the `where`; the engine tie is
`engineEmissionSV_engineTied`.

HONESTY DISPLAY (blueprint §4 B1, unchanged in substance): ν's SHAPE fields are
UNCONSTRAINED in this SV body — every `sel = none` ν is admitted at a decided
irr seam. Consequences, displayed: `tREAD` at `engineEmissionSV` is REFUTABLE
(junk shapes) — the trio is NOT claimed at SV; SV exists to discharge
tDECdec/tDECcor/tVERD-shaped work early. The C0 upgrade `engineEmission`
(ν := the TRM record) is where tREAD becomes provable. -/

/-- H6-B1 (body VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit B1):
the canonical site/verdict emission. `reaches` = realization by a coherent
`ReadsOf`-lawful machine history projecting (certificate-free, via
`machineEHist`) onto the seam; `emits` = the sel-none ν admission at a decided
irr seam realized by an `IrrHalts` run whose accumulator pair is the verdict;
`emitsHen` = the base-seam machine-record booking channel at `(1, f₀)`.
Shape fields of ν are deliberately NOT constrained (see the honesty display
in the section header). -/
noncomputable def engineEmissionSV (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : TerminalEmission p F where
  reaches f H := ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧ (machineEHist M).continuingPart = H
  emits f H ν EF := ν.sel = none ∧ DecIrrSeam H ∧
      (∀ ν' ∈ H.nodes, ν'.sel ≠ none) ∧
      ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        (machineEHist M).continuingPart = H ∧
        MovesT.IrrHalts M ∧ EF = (MovesT.accE M, MovesT.accF M)
  emitsHen f H EF := H.nodes = [] ∧ EF = (1, H.psi0.natDegree) ∧
      ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        (machineEHist M).continuingPart = H
  emits_terminal := fun _ _ _ _ h => h.1
  emits_reaches := fun _ _ _ _ h => by
    obtain ⟨-, -, -, M, hcoh, hread, hpart, -, -⟩ := h
    exact ⟨M, hcoh, hread, hpart⟩
  emitsHen_reaches := fun _ _ _ h => h.2.2
  reaches_continuing := fun _ H h ν hν => by
    obtain ⟨M, -, -, rfl⟩ := h
    have hmem : ν ∈ (machineEHist M).nodes.takeWhile
        (fun ν' => ν'.sel.isSome) := hν
    have hsome := List.mem_takeWhile_imp
      (p := fun ν' : ENodeData => ν'.sel.isSome) hmem
    exact Option.isSome_iff_ne_none.mp hsome

/-- H6-B1: the canonical emission IS engine-tied — `reaches` and `emits` are
definitionally the realization clauses `EngineTied` demands (the `emits` case
projects away the sel-none/decidedness/continuing conjuncts). -/
theorem engineEmissionSV_engineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    EngineTied n p F (engineEmissionSV n p F) where
  reaches_engine := fun _ _ h => h
  emits_irr_verdict := fun _ _ _ _ h _ => h.2.2.2

/-! ## Gate G2 — the POSITIVE terminal-seam gate (blueprint §4 Gates, fold
round 1 Codex finding 15's structural non-vacuity demand)

Spec (`lean/blueprints/HDISCHARGE_H6.md` §4 Gates G2, prose spec — no displayed
Lean block; the witness constructions are the gate's own content per the
III-A6c/HK23 gate discipline): "the SAME certified k′ = 0 seam with an emission
satisfying every row NON-VACUOUSLY — a witnessed reach AND a witnessed emitsHen
with EF = (1, f₀) (`HK23_twoNodeGatePos` style).  The all-False emission
satisfies `TerminalSeamHypsE` vacuously, so the gate MUST exhibit the positive
witnesses; it additionally needs `EngineTied` + `EngineCovers` versions at a
realized `ReadsOf` history (U31's `gate_readsOf_inert2` anchor) for the
D1a-shape non-vacuity."

Part A builds THE certified k′ = 0 seam of the G1/G2 spec (finding 15's
explicit demand): `H.nodes = []`, `a0 := 1`, `psi0 := X` (monic irreducible,
f₀ = 1); D := the canonical order-0 read `gmnDataOrder1` (A6b's positive face —
real corpus content); R := the canonical reader `gmnReaderOrder1`; `ConsF`
holds (vacuous node clause + rootOrd = a₀, via `multiplicity X X = 1`).

Part B is the emission: witnessed reach, witnessed `emitsHen` at
EF = (1, f₀) = (1, 1), every `TerminalSeamHypsE` row proved — the hen rows
(tDECdec hen leg, tDECcor hen leg, tVERDhen) FIRE on the witnesses; the irr/
`emits`-channel rows hold because this gate emission's `emits` never fires (a
k′ = 0 hen seam has no τ-irr channel; G1's countermodel is where the rows'
non-tautology is certified).  Packaged as one ∃-theorem, `henSeamGate_pos`.

Part C is the D1a-shape non-vacuity at a REALIZED `ReadsOf` history (U31's
`gate_readsOf_inert2` anchor): the `EngineCovers` face (the D1a covering
antecedent is realized and `engineEmissionSV` covers the realized seam), the
`EngineTied` face (B0's `reaches_engine` row FIRES there, returning the machine
realization), and D1a's parenthetical (the all-False emission FAILS the
covering implication at that seam).  `EngineCovers` itself is unit D1a's def
(unlanded at HEAD) — the faces here are its clauses INSTANTIATED, so D1a can
consume this gate without a forward reference. -/

/-! ### G2 Part A — the certified k′ = 0 seam -/

/-- G2 seam carrier: the k′ = 0 (root-only, no nodes) 𝔈-history at p = 2,
F = ZMod 2 — `nodes = []`, `a0 = 1`, `psi0 = X` (monic irreducible, f₀ = 1);
tower dressing `o2aGatePoly = X + 1` (monic, irreducible, ≠ X). -/
noncomputable def gatePosHist : EHist 2 (ZMod 2) where
  base := ⊤
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  a0 := 1
  ha0 := le_rfl
  nodes := []
  fld := fun _ => ⊤
  psihat := fun _ => o2aGatePoly
  hpsihat := fun _ =>
    ⟨o2aGatePoly_monic, o2aGatePoly_irreducible, o2aGatePoly_ne_X⟩

/-- The seam chain is empty: k′ = 0 requests no slopes. -/
theorem gatePos_slopes : (Theta gatePosHist).slopes = [] := rfl

theorem gatePos_hlen : (Theta gatePosHist).slopes.length ≤ 1 :=
  Nat.zero_le 1

/-- G2 seam datum: D := THE canonical order-0 read (A6b's positive face,
`gmnDataOrder1` — real corpus content, the corpus base Newton polygon +
residual/root orders through ι). -/
noncomputable def gatePosData :
    GMNData (Polynomial.X : Polynomial ℤ_[2]) (Theta gatePosHist) :=
  gmnDataOrder1 (Polynomial.X : Polynomial ℤ_[2]) (Theta gatePosHist)
    gateIota gateIota gatePos_hlen

/-! The corpus base read of f = X is EMPTY (its valuation support is the
single dot (1, 0), whose hull has one vertex and hence no sides) — computed
against the `OM/NewtonPolygon` heights-zero helpers, `negGate`-template. -/

private def gatePosSupport : Finset (ℕ × ℕ) := {(1, 0)}

private lemma gatePosSupport_nonempty : gatePosSupport.Nonempty :=
  ⟨(1, 0), by simp [gatePosSupport]⟩

open LeanUrat.OM in
/-- The valuation support of f = X over ℤ_[2]: the single dot (1, 0). -/
private lemma gatePos_valSupport :
    M2.valSupport 2 (Polynomial.X : Polynomial ℤ_[2]) = gatePosSupport := by
  have hchar := (M2.valSupport_facts 2 (Polynomial.X : Polynomial ℤ_[2])).1
  ext ⟨i, v⟩
  rw [hchar i v, gatePosSupport, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, rfl⟩
    match i with
    | 0 =>
        exfalso
        exact hne (by simp)
    | 1 =>
        rw [Prod.mk.injEq]
        exact ⟨rfl, by rw [M2.coeffVal, Polynomial.coeff_X_one,
          PadicInt.valuation_one]⟩
    | (n + 2) =>
        exfalso
        exact hne (by simp [Polynomial.coeff_X])
  · intro h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by rw [M2.coeffVal, Polynomial.coeff_X_one,
      PadicInt.valuation_one]⟩

open LeanUrat.OM in
/-- The hull of the single dot (1, 0): one vertex. -/
private lemma gatePos_npVertices :
    NewtonPolygon.npVertices gatePosSupport gatePosSupport_nonempty
      = [(1, 0)] := by
  have h0 : ∀ P ∈ gatePosSupport, P.2 = 0 := by
    intro P hP
    rw [gatePosSupport, Finset.mem_singleton] at hP
    subst hP
    rfl
  have himg : gatePosSupport.image Prod.fst = {1} := by decide
  have hd : NewtonPolygon.hullDotAt gatePosSupport gatePosSupport_nonempty 1
      = (1, 0) := by
    unfold NewtonPolygon.hullDotAt
    rw [NewtonPolygon.hullHeightAt_of_heights_zero _ gatePosSupport_nonempty h0]
  unfold NewtonPolygon.npVertices NewtonPolygon.npVerticesFull
    NewtonPolygon.hullAbscissae
  rw [NewtonPolygon.hullDots_of_heights_zero _ gatePosSupport_nonempty h0,
    himg, Finset.sort_singleton, List.map_cons, List.map_nil, hd]
  rfl

open LeanUrat.OM in
/-- One vertex ⇒ no sides. -/
private lemma gatePos_npSides :
    NewtonPolygon.npSides gatePosSupport gatePosSupport_nonempty = [] := by
  rw [NewtonPolygon.npSides, gatePos_npVertices]
  rfl

open LeanUrat.OM in
private lemma gatePos_sideList :
    sideList (Polynomial.X : Polynomial ℤ_[2]) = [] := by
  have hne : (M2.valSupport 2 (Polynomial.X : Polynomial ℤ_[2])).Nonempty := by
    rw [gatePos_valSupport]
    exact gatePosSupport_nonempty
  rw [sideList, dif_pos hne,
    NewtonPolygon.npSides_congr _ gatePosSupport hne gatePosSupport_nonempty
      gatePos_valSupport,
    gatePos_npSides]

/-- The compiled corpus base read of f = X: NO principal side (the single-dot
polygon has no side at all — in particular none of negative slope). -/
theorem principalData_X_nil :
    principalData (Polynomial.X : Polynomial ℤ_[2]) = [] := by
  rw [principalData, principalSideList, gatePos_sideList]
  rfl

/-- The canonical order-0 datum at the seam satisfies the `OL5` API row
(vacuously: the empty chain requests no slope). -/
theorem gatePosData_OL5 :
    OL5 (Polynomial.X : Polynomial ℤ_[2]) (Theta gatePosHist) gatePosData := by
  intro i S T _ _ hS _
  exfalso
  have hnone : requestedSlope (Theta gatePosHist) i = none := by
    simp [requestedSlope, gatePos_slopes]
  rw [HasRequestedSlope, hnone] at hS
  simp at hS

/-- The canonical order-0 datum at the seam satisfies the `OL3min` API row
(vacuously: every side list of the seam datum is empty — the deep levels by
construction, level 0 by `principalData_X_nil`). -/
theorem gatePosData_OL3min :
    OL3min (Polynomial.X : Polynomial ℤ_[2]) (Theta gatePosHist) gatePosData := by
  intro i S hS
  exfalso
  have hnil : gatePosData.principalSides i = [] := by
    rcases i with _ | i
    · show (if (0 : ℕ) = 0 then principalData (Polynomial.X : Polynomial ℤ_[2])
        else []) = []
      rw [if_pos rfl, principalData_X_nil]
    · rfl
  rw [hnil] at hS
  exact List.not_mem_nil hS

/-- G2 seam reader: R := THE canonical reader (`gmnReaderOrder1`, unit
III-A6b's builder) on the canonical order-0 datum. -/
noncomputable def gatePosReader :
    GMNReader (Polynomial.X : Polynomial ℤ_[2]) (Theta gatePosHist)
      gatePosData :=
  gmnReaderOrder1 gatePosData_OL5 gatePosData_OL3min

/-- The canonical root order at the seam is 1: `ord_X(X̄) = 1`
(`multiplicity X X = 1`). -/
theorem gatePosData_rootOrder : gatePosData.rootOrder = 1 := by
  show rootOrder0 (Polynomial.X : Polynomial ℤ_[2]) (Theta gatePosHist)
    gateIota = 1
  rw [rootOrder0, Polynomial.map_X, Polynomial.map_X]
  exact multiplicity_self

/-- G2 seam certification, `ConsF` half: `Cons_f(𝐇°)` HOLDS at the seam —
the node clause is vacuous (k′ = 0) and `rootOrd = a₀ = 1` is the genuine
`multiplicity` computation `gatePosData_rootOrder`. -/
theorem gatePos_consF :
    ConsF (Polynomial.X : Polynomial ℤ_[2]) gatePosHist gatePosData
      gatePosReader := by
  refine ⟨?_, ?_⟩
  · change gatePosData.rootOrder = gatePosHist.a0
    rw [gatePosData_rootOrder]
    rfl
  · intro i ν hν
    exfalso
    have hnil : gatePosHist.continuingPart.nodes = [] := rfl
    rw [hnil] at hν
    simp at hν

/-- G2 seam certification, `ReadThroughIota` half: the canonical order-0 read
IS certified at the seam (A6b's positive face, instantiated). -/
theorem gatePos_readThroughIota :
    ReadThroughIota (Polynomial.X : Polynomial ℤ_[2]) gatePosHist
      gatePosData :=
  readThroughIota_order1_gate _ gatePosHist gateIota gateIota gatePos_hlen

/-- The seam is DECIDED on the hen channel: k′ = 0 with a₀ = 1 (the Hensel
booking disjunct — no −∞ side needed). -/
theorem gatePos_decHenSeam :
    DecHenSeam (Polynomial.X : Polynomial ℤ_[2]) gatePosHist gatePosData :=
  ⟨rfl, Or.inl rfl⟩

/-! ### G2 Part B — the positive emission and the packaged gate -/

/-- G2 gate emission: reaches EXACTLY the certified seam, emits nothing on the
site/verdict channel (a k′ = 0 hen seam has no τ-irr channel), and books the
machine-record channel at EF = (1, f₀) = (1, 1). -/
noncomputable def gatePosEmission : TerminalEmission 2 (ZMod 2) where
  reaches f H := f = Polynomial.X ∧ H = gatePosHist
  emits _ _ _ _ := False
  emitsHen f H EF := f = Polynomial.X ∧ H = gatePosHist ∧ EF = (1, 1)
  emits_terminal := fun _ _ _ _ h => False.elim h
  emits_reaches := fun _ _ _ _ h => False.elim h
  emitsHen_reaches := fun _ _ _ h => ⟨h.1, h.2.1⟩
  reaches_continuing := fun _ H h ν hν => by
    have hH : H = gatePosHist := h.2
    subst hH
    exact absurd hν List.not_mem_nil

/-- G2: EVERY `TerminalSeamHypsE` row holds at the gate emission.  The hen
rows fire non-vacuously (see `henSeamGate_pos` for the witnesses); the
`emits`-channel rows hold because the gate emission's `emits` never fires. -/
theorem gatePos_seamHyps :
    TerminalSeamHypsE 2 (ZMod 2) gatePosEmission where
  tDECdec := fun f H _ _ _ _ hre => by
    have hre' : f = Polynomial.X ∧ H = gatePosHist := hre
    obtain ⟨rfl, rfl⟩ := hre'
    refine ⟨fun hirr => absurd rfl hirr.1, fun _ => ⟨(1, 1), ?_⟩⟩
    exact ⟨rfl, rfl, rfl⟩
  tDECcor := fun f H _ _ _ _ => by
    refine ⟨fun ν EF h => False.elim h, fun EF h => ?_⟩
    have h' : f = Polynomial.X ∧ H = gatePosHist ∧ EF = (1, 1) := h
    obtain ⟨rfl, rfl, rfl⟩ := h'
    exact ⟨rfl, Or.inl rfl⟩
  tREAD := fun _ _ _ _ _ _ _ _ h _ => False.elim h
  tVERD := fun _ _ _ _ _ _ _ _ h _ => False.elim h
  tVERDhen := fun f H EF _ _ _ _ hemit _ => by
    have h' : f = Polynomial.X ∧ H = gatePosHist ∧ EF = (1, 1) := hemit
    obtain ⟨rfl, rfl, rfl⟩ := h'
    have h1 : gatePosHist.psi0 = Polynomial.X := rfl
    rw [h1, Polynomial.natDegree_X]

/-- G2 witness: the reach IS witnessed at the certified seam. -/
theorem gatePos_reaches :
    gatePosEmission.reaches (Polynomial.X : Polynomial ℤ_[2]) gatePosHist :=
  ⟨rfl, rfl⟩

/-- G2 witness: `emitsHen` IS witnessed at the certified seam, at
EF = (1, f₀) = (1, 1). -/
theorem gatePos_emitsHen :
    gatePosEmission.emitsHen (Polynomial.X : Polynomial ℤ_[2]) gatePosHist
      (1, 1) :=
  ⟨rfl, rfl, rfl⟩

/-- f₀ = 1 at the seam (psi0 = X). -/
theorem gatePos_f0 : gatePosHist.psi0.natDegree = 1 :=
  Polynomial.natDegree_X

/-- **GATE G2, PACKAGED (blueprint §4 Gates G2; `HK23_twoNodeGatePos` style;
fold round 1 Codex finding 15's structural demand).**  There IS an emission
satisfying every repaired (H6) row over a CERTIFIED k′ = 0 seam — witnessed
reach AND witnessed `emitsHen` at EF = (1, f₀) — with the certification
antecedents (`ReadThroughIota` at the canonical order-0 read + `ConsF` at the
canonical reader) REALIZED, the seam decided on the hen channel, and the seam
shape pinned (`nodes = []`, `a₀ = 1`, f₀ = 1).  The repaired rows are hereby
satisfiable NON-VACUOUSLY: the hen legs of tDECdec/tDECcor and tVERDhen all
fire on the displayed witnesses (G1 is the matching countermodel gate — the
rows are not tautologies). -/
theorem henSeamGate_pos :
    ∃ (E : TerminalEmission 2 (ZMod 2)) (f : Polynomial ℤ_[2])
      (H : EHist 2 (ZMod 2)) (D : GMNData f (Theta H))
      (R : GMNReader f (Theta H) D),
      TerminalSeamHypsE 2 (ZMod 2) E ∧
      ReadThroughIota f H D ∧ ConsF f H D R ∧
      H.nodes = [] ∧ H.a0 = 1 ∧ H.psi0.natDegree = 1 ∧
      DecHenSeam f H D ∧
      E.reaches f H ∧
      E.emitsHen f H (1, H.psi0.natDegree) := by
  refine ⟨gatePosEmission, Polynomial.X, gatePosHist, gatePosData,
    gatePosReader, gatePos_seamHyps, gatePos_readThroughIota, gatePos_consF,
    rfl, rfl, gatePos_f0, gatePos_decHenSeam, gatePos_reaches, ?_⟩
  rw [gatePos_f0]
  exact gatePos_emitsHen

/-! ### G2 Part C — `EngineTied` + `EngineCovers` faces at a realized
`ReadsOf` history (U31's `gate_readsOf_inert2` anchor; D1a-shape non-vacuity)

`EngineCovers` (unit D1a, unlanded at HEAD) is
`∀ f H, (∃ M, HistoryCoherent M ∧ ReadsOf n p F f M ∧
(machineEHist M).continuingPart = H) → E.reaches f H`; the gates below
instantiate its antecedent AND its conclusion at a compiled realized history,
so the D1a covering row is demonstrably non-vacuous — and the all-False
emission demonstrably fails it — without forward-referencing the def. -/

/-- G2/EngineCovers face: at U31's realized `ReadsOf` history (p = 2, F = F4,
n = 2, the root-only inert read), the D1a covering antecedent IS realized and
the canonical emission `engineEmissionSV` COVERS the realized seam. -/
theorem gateReadsOf_engineCovers_pos :
    ∃ (f : Polynomial ℤ_[2]) (H : EHist 2 LeanUrat.MovesJ.F4),
      (∃ M : MovesC.History 2 LeanUrat.MovesJ.F4,
        MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf 2 LeanUrat.MovesJ.F4 2 f M ∧
        (machineEHist M).continuingPart = H) ∧
      (engineEmissionSV 2 2 LeanUrat.MovesJ.F4).reaches f H := by
  obtain ⟨M, f, -, -, hread⟩ := LeanUrat.MovesJ.gate_readsOf_inert2
  have hcoh : MovesC.HistoryCoherent M := hread.2.2.1
  exact ⟨f, (machineEHist M).continuingPart, ⟨M, hcoh, hread, rfl⟩,
    ⟨M, hcoh, hread, rfl⟩⟩

/-- G2/EngineTied face: at the same realized seam, B0's `reaches_engine` row
FIRES — applied to the witnessed reach it returns a coherent `ReadsOf`-lawful
machine realization of the seam (the row is consumed, not restated). -/
theorem gateReadsOf_engineTied_pos :
    ∃ (f : Polynomial ℤ_[2]) (H : EHist 2 LeanUrat.MovesJ.F4),
      (engineEmissionSV 2 2 LeanUrat.MovesJ.F4).reaches f H ∧
      ∃ M : MovesC.History 2 LeanUrat.MovesJ.F4,
        MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf 2 LeanUrat.MovesJ.F4 2 f M ∧
        (machineEHist M).continuingPart = H := by
  obtain ⟨f, H, -, hreach⟩ := gateReadsOf_engineCovers_pos
  exact ⟨f, H, hreach,
    (engineEmissionSV_engineTied 2 2 LeanUrat.MovesJ.F4).reaches_engine
      f H hreach⟩

/-- The all-False emission (every channel empty).  `EngineTied` holds for it
vacuously — which is exactly why D1a's covering clause is load-bearing. -/
def allFalseEmission (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : TerminalEmission p F where
  reaches _ _ := False
  emits _ _ _ _ := False
  emitsHen _ _ _ := False
  emits_terminal := fun _ _ _ _ h => False.elim h
  emits_reaches := fun _ _ _ _ h => h
  emitsHen_reaches := fun _ _ _ h => h
  reaches_continuing := fun _ _ h => False.elim h

/-- D1a's parenthetical, compiled (the covering clause is NOT trivially true):
at the realized `ReadsOf` seam the all-False emission FAILS the covering
implication — its `reaches` is empty where the antecedent is witnessed. -/
theorem gateReadsOf_allFalse_notCovering :
    ∃ (f : Polynomial ℤ_[2]) (H : EHist 2 LeanUrat.MovesJ.F4),
      (∃ M : MovesC.History 2 LeanUrat.MovesJ.F4,
        MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf 2 LeanUrat.MovesJ.F4 2 f M ∧
        (machineEHist M).continuingPart = H) ∧
      ¬ (allFalseEmission 2 LeanUrat.MovesJ.F4).reaches f H := by
  obtain ⟨f, H, hM, -⟩ := gateReadsOf_engineCovers_pos
  exact ⟨f, H, hM, fun h => h⟩

end LeanUrat.Scaffold.HDischarge.H6
