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
import LeanUrat.MovesU.BridgeD4_vtLaws

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

/-! ## Unit B2 — (T-VERD) dress commutation at the engine

Blueprint spec (`lean/blueprints/HDISCHARGE_H6.md` §4 unit B2, MED-HARD —
retagged at fold round 1, Codex finding 12): the dress commutation
`eAccE (machineProj M hM).val.continuingPart = MovesT.accE M` (resp.
eAccF/accF with the f₀ root-datum split — §3.4's flagged reconciliation),
"statement finalized against `machineEHist`'s fieldwise lemmas at E-phase";
then `tVERD` for `engineEmissionSV` on the irr leg.

FINALIZATION RECORD (this unit's E-phase duty, executed 2026-08-01):
* Per the B0 FOOTPRINT RULE the statements bind `machineEHist`
  (= `machineProj_val`, certificate-free), NOT `machineProj` — binding the
  latter would inherit CU1's W3 `sorryAx` through the bundled `EWF`
  certificate. `hM`'s coherence content rides as the explicit
  `MovesC.HistoryCoherent M` hypothesis where consumed.
* **THE §3.4 FLAGGED RECONCILIATION IS CHECKED — the as-built `nodeToE` does
  NOT refute the f₀ factorization.** The two factorizations reconcile
  through the root-datum split exactly as the CUC prices it:
  - accF (UNCONDITIONAL): the machine's `accF = ∏_{M.nodes} ν.g` opens as
    `root.g · ∏_{tail} ν.g` (`accF_rootSplit`); the E-side's f₀-included
    `eAccF = f₀ · ∏ (sel g's)` has f₀ = deg ψ̂₀ = deg root.ψ, and the node
    carrier row `hψdeg : ψ.natDegree = g` pins `f₀ = root.g`
    (`rootRead_g_eq_f0`) — root read = residue-factor choice, verbatim. The
    tail selections transport by `nodeToE_sel` (`sel = some (g, μ)` ⇒
    `sel.elim 1 Prod.fst = g`), so the products agree field by field.
  - accE (CONDITIONAL — the honest boundary, displayed): the machine's
    `accE = ∏_{M.nodes} ν.e` carries the ROOT read's e, which the E-side
    `eAccE = ∏_{𝐇°} ν.e` does not. They agree because `root.e = 1` under
    `HistoryCoherent` — the RG-2 recording-fence clause (`species ≠
    recentering → e = 1` at every node WITH a successor) fired at node 0
    via `root_iff` (`rootRead_e_eq_one`). At a ROOT-ONLY history (empty
    seam, k′ = 0) the fence does not reach the root and `accE M = root.e`
    is genuinely unconstrained — there the commutation is NOT claimed
    (hypothesis `hne`); that boundary is exactly the CUC §9.2 hen channel
    ((accE₀, accF₀) = (1, f₀), `tVERDhen`'s leg, A1's gate), never the irr
    leg, where `DecIrrSeam` forces the seam nonempty.
* `continuingPart` is the IDENTITY on projected histories
  (`machineEHist_continuingPart_nodes`): every `nodeToE` record carries
  `sel = some _`, so the takeWhile keeps the whole node list.
* T-V8 `acc_pos` (quarried by the spec) was NOT needed: `engineEmissionSV`'s
  emits channel books the bare pair `(accE M, accF M)` and `terminalDatumD`'s
  verdict is guard-free, so no max-guards arise to kill. -/

section UnitB2

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- B2 helper: the dressed continuing part of a projection keeps EVERY node —
each emitted record is selection-carrying (`nodeToE_sel`), so the
`takeWhile sel.isSome` is the identity on `machineEHist M`'s node list. -/
theorem machineEHist_continuingPart_nodes (M : MovesC.History p F) :
    (machineEHist M).continuingPart.nodes = M.nodes.tail.map nodeToE :=
  List.takeWhile_eq_self_iff.mpr (fun ν hν => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hν
    rfl)

/-- B2, the machine-side root-datum split (E-component): the machine
accumulator `accE = ∏_{M.nodes} ν.e` opens as the ROOT read's e times the
tail product. -/
theorem accE_rootSplit (M : MovesC.History p F) :
    MovesT.accE M
      = (M.nodes.head M.nonempty).e * (M.nodes.tail.map fun m => m.e).prod := by
  have hcons : M.nodes.head M.nonempty :: M.nodes.tail = M.nodes :=
    List.cons_head_tail _
  calc MovesT.accE M
      = ((M.nodes.head M.nonempty :: M.nodes.tail).map fun ν => ν.e).prod := by
        rw [hcons]; rfl
    _ = _ := by rw [List.map_cons, List.prod_cons]

/-- B2, the machine-side root-datum split (F-component): the machine
accumulator `accF = ∏_{M.nodes} ν.g` opens as the ROOT read's g times the
tail product — the root read IS a residue-factor choice, its g the factor
the E-side books as f₀. -/
theorem accF_rootSplit (M : MovesC.History p F) :
    MovesT.accF M
      = (M.nodes.head M.nonempty).g * (M.nodes.tail.map fun m => m.g).prod := by
  have hcons : M.nodes.head M.nonempty :: M.nodes.tail = M.nodes :=
    List.cons_head_tail _
  calc MovesT.accF M
      = ((M.nodes.head M.nonempty :: M.nodes.tail).map fun ν => ν.g).prod := by
        rw [hcons]; rfl
    _ = _ := by rw [List.map_cons, List.prod_cons]

/-- B2, the root ramification unit: under `HistoryCoherent`, a root read WITH
a successor has `e = 1` — the recording-fence clause (`species ≠ recentering
→ e = 1`, HistoryCoherent step clause) fired at node 0 (species `root` by
`root_iff`, and `root ≠ recentering`). NOT claimed at root-only histories
(the fence only reaches nodes with successors) — hence `eAccE_dressCommute`'s
seam-nonemptiness hypothesis. -/
theorem rootRead_e_eq_one (M : MovesC.History p F)
    (hcoh : MovesC.HistoryCoherent M) (hlen : 1 < M.nodes.length) :
    (M.nodes.head M.nonempty).e = 1 := by
  have hroot : (M.nodes[0]'(by omega)).species = MovesC.ReadSpecies.root :=
    (M.root_iff 0 (by omega)).mpr rfl
  have hsp : (M.nodes[0]'(by omega)).species ≠ MovesC.ReadSpecies.recentering := by
    rw [hroot]; exact fun h => nomatch h
  have he1 : (M.nodes[0]'(by omega)).e = 1 := ((hcoh.2.2.2 0 hlen).2.1 hsp).1
  rw [List.head_eq_getElem]
  exact he1

/-- B2, the f₀ pin (the §3.4 reconciliation's crux, UNCONDITIONAL): the
dressed seam's f₀ = deg ψ̂₀ IS the root read's residual degree g — the node
carrier row `hψdeg` (ψ monic irreducible of degree g), no coherence
consumed. -/
theorem rootRead_g_eq_f0 (M : MovesC.History p F) :
    (machineEHist M).continuingPart.psi0.natDegree
      = (M.nodes.head M.nonempty).g :=
  (M.nodes.head M.nonempty).hψdeg

/-- **B2 dress commutation, F-component (UNCONDITIONAL)**: the E-side
f₀-included accumulator through the dressed continuing part equals the
machine's `accF` — `f₀ · ∏_{tail} (sel g) = root.g · ∏_{tail} g` via the
f₀ pin (`rootRead_g_eq_f0`) and the `nodeToE` selection transport. The §3.4
flagged reconciliation, resolved POSITIVELY at the as-built `nodeToE`. -/
theorem eAccF_dressCommute (M : MovesC.History p F) :
    eAccF (machineEHist M).continuingPart = MovesT.accF M := by
  have hmapF : ((M.nodes.tail.map nodeToE).map fun ν => (ν.sel.elim 1 Prod.fst))
      = M.nodes.tail.map fun m => m.g := by
    rw [List.map_map]; rfl
  unfold eAccF
  rw [machineEHist_continuingPart_nodes M, hmapF, accF_rootSplit M,
    rootRead_g_eq_f0 M]

/-- **B2 dress commutation, E-component**: the E-side ramification
accumulator through the dressed continuing part equals the machine's `accE`,
under coherence at a NONEMPTY seam (the honest boundary — see the section
header; `DecIrrSeam` supplies `hne` on the irr leg, and the empty-seam
boundary is the hen channel's `(1, f₀)` booking, not this lemma's claim). -/
theorem eAccE_dressCommute (M : MovesC.History p F)
    (hcoh : MovesC.HistoryCoherent M)
    (hne : (machineEHist M).continuingPart.nodes ≠ []) :
    eAccE (machineEHist M).continuingPart = MovesT.accE M := by
  have hnodes := machineEHist_continuingPart_nodes M
  have hlen : 1 < M.nodes.length := by
    rw [hnodes] at hne
    have htail : M.nodes.tail ≠ [] := fun h => hne (by rw [h]; rfl)
    have h1 : 0 < M.nodes.tail.length := List.length_pos_of_ne_nil htail
    have h2 : M.nodes.tail.length = M.nodes.length - 1 := List.length_tail
    omega
  have hmapE : ((M.nodes.tail.map nodeToE).map fun ν => ν.e)
      = M.nodes.tail.map fun m => m.e := by
    rw [List.map_map]; rfl
  unfold eAccE
  rw [hnodes, hmapE, accE_rootSplit M, rootRead_e_eq_one M hcoh hlen, one_mul]

/-- **B2 (T-VERD) dress commutation at the engine, packaged** (blueprint §4
B2's displayed pair, finalized at `machineEHist` per the B0 footprint rule):
`(eAccE, eAccF)` of the dressed continuing part IS the machine accumulator
pair `(accE M, accF M)`, under coherence at a nonempty seam. -/
theorem dress_commutation (M : MovesC.History p F)
    (hcoh : MovesC.HistoryCoherent M)
    (hne : (machineEHist M).continuingPart.nodes ≠ []) :
    (eAccE (machineEHist M).continuingPart,
      eAccF (machineEHist M).continuingPart)
      = (MovesT.accE M, MovesT.accF M) := by
  rw [eAccE_dressCommute M hcoh hne, eAccF_dressCommute M]

end UnitB2

/-- **B2, `tVERD` for `engineEmissionSV` on the irr leg** (the A7 row shape,
VERBATIM at `E := engineEmissionSV n p F`): every emitted verdict pair is the
A4-forced terminal datum's. The emits channel fires only at `DecIrrSeam`
seams, so the forced verdict is the `(eAccE, eAccF)` booking, and the
realizing machine run's pair `(accE M, accF M)` matches by the dress
commutation — `DecIrrSeam`'s nonemptiness IS the E-component's boundary
hypothesis. (`tVERDhen`, the hen channel, is not this unit's leg.) -/
theorem engineEmissionSV_tVERD (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    ∀ f H ν EF (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
      ReadThroughIota f H D → ConsF f H D R →
      (engineEmissionSV n p F).emits f H ν EF → DecSeam f H D →
      EF = (terminalDatumD f H D).verdict := by
  intro f H ν EF D R _ _ hemit _
  obtain ⟨-, hdec, -, M, hcoh, -, hpart, -, rfl⟩ := hemit
  have hv : (terminalDatumD f H D).verdict = (eAccE H, eAccF H) := by
    unfold terminalDatumD
    exact if_pos hdec
  rw [hv]
  subst hpart
  rw [eAccE_dressCommute M hcoh hdec.1, eAccF_dressCommute M]

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

/-! ## Unit B3a — (T-DEC-dec) at the engine: the τ-irr dress theorem and
`tDECdec`'s irr leg for `engineEmissionSV`

Blueprint charge (`lean/blueprints/HDISCHARGE_H6.md` §4 unit B3a, prose —
transcribed): "(T-DEC-dec) at the engine: via `MovesT.irr_iff_mu_one` (PROVED)
+ the nodeToE sel-transport — a lawful coherent M IrrHalts iff its dressed
continuing part is `DecIrrSeam`; conclude `tDECdec`'s irr leg for
`engineEmissionSV`. Hen leg (a₀ ≥ 2 booking from the root-datum split) may
split off as B3a′. Deps: B1; quarry `irr_iff_mu_one`, `HistLawful`."

STATEMENT DESIGN, ON RECORD (the blueprint displays no Lean block for B3a
itself; every consumed shape is displayed elsewhere and bound VERBATIM —
`DecIrrSeam` at A2, the `tDECdec` row at A7, the `engineEmissionSV` body at
B1, `machineEHist`/`nodeToE` fieldwise at CU1):

* **The dress theorem** (`irrHalts_iff_decIrrSeam`) renders the prose iff with
  the NONEMPTY-TAIL hypothesis `M.nodes.tail ≠ []` — the root-datum corner
  already on record at CU1's III-A5 footprint note ("lands at ... `a0` when
  `M.nodes.length = 1` ... but at the last projected node's `sel` when
  `2 ≤ M.nodes.length`"; "two inequivalent renderings ... two-case split vs. a
  nonempty-tail hypothesis"): a machine history whose ONLY node is the root
  read dresses to a k′ = 0 seam carrying `a0 = root.μ` — the HEN channel, not
  a τ-irr seam — and B3a's prose splits that corner off to B3a′.  On the
  DEC-consumption side the corner is invisible: `DecIrrSeam H` forces the seam
  nonempty, hence the machine tail nonempty (`decIrrSeam` → `htail` below).
* **Lawfulness rides as the explicit fenced hypothesis** `MovesT.HistLawful
  p n M` — MovesT/Defs' fenced conditionality VERBATIM: "`HistoryCoherent`
  alone does NOT imply this; discharge is QUEUED ON Q1 (§4) — until then
  `hlaw : HistLawful p n H` is an explicit hypothesis."  Accordingly the
  packaged `engineEmissionSV_tDECdec` is the A7 `tDECdec` row at
  `E := engineEmissionSV n p F` with the row's reach antecedent strengthened
  to a LAWFUL reach (the ∃-witness additionally `HistLawful`); the bare-row
  form is NOT claimed — its irr leg would demand lawfulness of an arbitrary
  coherent `ReadsOf` realizer, exactly the Q1 residue, and asserting it here
  would discharge that fence by fiat.
* The sel-transport (machine `Node.μ/g` ↦ E-side `ENodeData.sel`) is
  `nodeToE_sel`, CU1's per-field lemma — cited, not re-proved (§3.1(b)).
* FOOTPRINT: everything binds `machineEHist` (certificate-free), never
  `machineProj` — B0's footprint rule; the W3 sorry is NOT inherited
  (§3.1(a); verify at gate via `#print axioms`, all rows Lean-core).
-/

/-- Every node of a dressed machine history carries a selection (`nodeToE`
always records `sel = some (g, μ)` — the sel-transport `nodeToE_sel`), so the
dressed history IS its own continuing part: the `takeWhile` fence of
`EHist.continuingPart` keeps everything. -/
theorem machineEHist_continuingPart {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (M : MovesC.History p F) :
    (machineEHist M).continuingPart = machineEHist M := by
  show { machineEHist M with
    nodes := (machineEHist M).nodes.takeWhile fun ν => ν.sel.isSome }
      = machineEHist M
  rw [List.takeWhile_eq_self_iff.mpr ?_]
  · intro ν hν
    rw [machineEHist_nodes] at hν
    rcases List.mem_map.mp hν with ⟨m, -, rfl⟩
    rw [nodeToE_sel]
    rfl

/-- A list with a nonempty tail has the tail's last element as its own:
`getLast?` sees through the head. -/
private theorem getLast?_eq_tail_getLast? {α : Type*} {l : List α}
    (h : l.tail ≠ []) : l.getLast? = l.tail.getLast? := by
  match l, h with
  | [], h => exact absurd rfl h
  | [a], h => exact absurd rfl h
  | a :: b :: t, _ => exact List.getLast?_cons_cons

/-- **H6-B3a, THE τ-IRR DRESS THEOREM** (blueprint §4 unit B3a prose,
transcribed: "a lawful coherent M IrrHalts iff its dressed continuing part is
`DecIrrSeam`"): for a machine history with a continuing read on record
(`M.nodes.tail ≠ []` — the root-datum corner split off to B3a′, see the
section header), under lawfulness the τ-irr halt is EXACTLY seam decidedness
of the dressed continuing part.  Machine face: `MovesT.irr_iff_mu_one`
(IrrHalts ⟺ μ_last = 1, PROVED).  Transport: `machineEHist_nodes` +
`nodeToE_sel` at the last node.  Coherence rides per the blueprint prose
(binder `_hcoh`); the iff itself consumes only lawfulness — displayed, not
hidden. -/
theorem irrHalts_iff_decIrrSeam {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (n : ℕ) (M : MovesC.History p F)
    (_hcoh : MovesC.HistoryCoherent M) (hlaw : MovesT.HistLawful p n M)
    (htail : M.nodes.tail ≠ []) :
    MovesT.IrrHalts M ↔ DecIrrSeam (machineEHist M).continuingPart := by
  have hne : M.nodes ≠ [] := M.nonempty
  have hm : M.nodes.getLast? = some (M.nodes.getLast hne) :=
    List.getLast?_eq_some_getLast hne
  rw [MovesT.irr_iff_mu_one M n hlaw (M.nodes.getLast hne) hm,
    machineEHist_continuingPart]
  unfold DecIrrSeam
  rw [machineEHist_nodes, List.getLast?_map, ← getLast?_eq_tail_getLast? htail,
    hm]
  simp only [Option.map_some, Option.elim_some, nodeToE_sel, ne_eq,
    List.map_eq_nil_iff, htail, not_false_eq_true, true_and,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨(M.nodes.getLast hne).g, rfl, h⟩
  · rintro ⟨g, -, h⟩
    exact h

/-- **H6-B3a — `tDECdec`'s irr leg for `engineEmissionSV`** (the A7 row's irr
conjunct at `E := engineEmissionSV n p F`, the reach ∃-witness unpacked and
carrying the fenced `HistLawful` explicitly): a lawful coherent `ReadsOf`
realizer of a decided τ-irr seam books there — the emission fires with the
sel-none record `nuT1` and THE machine accumulator verdict
`(accE M, accF M)`.  Route: `DecIrrSeam H` forces the machine tail nonempty,
the dress theorem's ← direction yields `MovesT.IrrHalts M`, and B1's `emits`
body is assembled witness-by-witness (the continuing clause is the interface
law `reaches_continuing`, consumed, not re-proved). -/
theorem engineEmissionSV_tDECdec_irr (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    ∀ (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
      (R : GMNReader f (Theta H) D),
      ReadThroughIota f H D → ConsF f H D R →
      ∀ M : MovesC.History p F,
        MovesC.HistoryCoherent M →
        LeanUrat.MovesJ.ReadsOf p F n f M →
        MovesT.HistLawful p n M →
        (machineEHist M).continuingPart = H →
        DecIrrSeam H → ∃ ν EF, (engineEmissionSV n p F).emits f H ν EF := by
  intro f H D R _ _ M hcoh hread hlaw hpart hdec
  subst hpart
  have htail : M.nodes.tail ≠ [] := by
    have h1 := hdec.1
    rw [machineEHist_continuingPart, machineEHist_nodes] at h1
    intro h
    rw [h] at h1
    simp at h1
  have hirr : MovesT.IrrHalts M :=
    (irrHalts_iff_decIrrSeam n M hcoh hlaw htail).mpr hdec
  refine ⟨nuT1, (MovesT.accE M, MovesT.accF M), rfl, hdec, ?_,
    M, hcoh, hread, rfl, hirr, rfl⟩
  exact (engineEmissionSV n p F).reaches_continuing f _ ⟨M, hcoh, hread, rfl⟩

/-- **H6-B3a — `tDECdec`'s hen leg for `engineEmissionSV`** (the A7 row's hen
conjunct at `E := engineEmissionSV n p F`): at the SV interface the
machine-record booking channel fires DEFINITIONALLY at every reached
`DecHenSeam` — `emitsHen`'s three conjuncts are the seam's `nodes = []`, the
pinned pair `(1, f₀)`, and the reach witness.  No root-datum content is
claimed here: the machine-side characterization of hen bookings (the a₀ ≥ 2
split of the root datum) is B3a′ / the C0-upgrade territory, per the
blueprint's split-off clause. -/
theorem engineEmissionSV_tDECdec_hen (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    ∀ (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
      (R : GMNReader f (Theta H) D),
      ReadThroughIota f H D → ConsF f H D R →
      (engineEmissionSV n p F).reaches f H →
      DecHenSeam f H D → ∃ EF, (engineEmissionSV n p F).emitsHen f H EF := by
  intro f H D R _ _ hre hdec
  exact ⟨(1, H.psi0.natDegree), hdec.1, rfl, hre⟩

/-- **H6-B3a, PACKAGED: (T-DEC-dec) at the engine** — the A7 `tDECdec` row
shape at `E := engineEmissionSV n p F`, both legs, with the row's reach
antecedent `E.reaches f H` strengthened to a LAWFUL reach: the realizing
history additionally satisfies `MovesT.HistLawful p n M` (the fenced Q1
conditionality of MovesT/Defs, displayed as an explicit hypothesis — see the
section header; the bare-row form is NOT claimed).  Consumers (B3b's leaf
catalogue, D1a's witness assembly) thread the lawful reach. -/
theorem engineEmissionSV_tDECdec (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    ∀ (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
      (R : GMNReader f (Theta H) D),
      ReadThroughIota f H D → ConsF f H D R →
      (∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        MovesT.HistLawful p n M ∧
        (machineEHist M).continuingPart = H) →
      (DecIrrSeam H → ∃ ν EF, (engineEmissionSV n p F).emits f H ν EF) ∧
      (DecHenSeam f H D → ∃ EF, (engineEmissionSV n p F).emitsHen f H EF) := by
  intro f H D R hiota hcons hM
  obtain ⟨M, hcoh, hread, hlaw, hpart⟩ := hM
  exact ⟨engineEmissionSV_tDECdec_irr n p F f H D R hiota hcons
      M hcoh hread hlaw hpart,
    engineEmissionSV_tDECdec_hen n p F f H D R hiota hcons
      ⟨M, hcoh, hread, hpart⟩⟩

/-! ## Unit B3b — (T-DEC-cor) at the engine: the leaf catalogue, the `NsFree`
fence, and `tDECcor` for `engineEmissionSV` with `DeepCorner` never reached

Blueprint charge (`lean/blueprints/HDISCHARGE_H6.md` §4 unit B3b, prose —
transcribed): "(T-DEC-cor) at the engine: the leaf catalogue (leaf ⇒ IrrHalts ∨
hen-booked ∨ ns-booked) + `NsFree` fencing (Unit C's landed `bridgeTree`
conjunct) ⇒ `tDECcor` for `engineEmissionSV` with `DeepCorner` never reached.
FOLD ROUND 1 (Codex findings 9/13 accepted): NO sorry — if the catalogue lemma
is absent from the corpus, it lands as the NAMED HYPOTHESIS ROW `LeafCatalogue
(p F) : Prop` (displayed clause list; PART OF THIS GROUP'S RESIDUE, priced at
the disposition table) and B3b's theorem is stated CONDITIONAL on it; the row
routes to the GD-4 owner brief. The corner-unreachability claim is
ENGINE-strength only (§3.2(b) stands). Deps: B1, B3a; quarry
`E9_fiberDisjoint`, `IrrHaltsAsChild`, `MovesT.NsFree`, `bridgeTree`."

STATEMENT DESIGN, ON RECORD (the blueprint displays no Lean block for B3b
itself; every consumed shape is displayed elsewhere and bound VERBATIM —
`DecSeam`/`DeepCorner`/`DecHenSeam` at A2/A3, the `tDECcor` row at A7, the
`engineEmissionSV` body at B1, the `LeafCatalogue (p F) : Prop` keying at the
B3b block, `NsFree`/`fiberAt`/`IsMaximalIn` at MovesT/Defs as built,
`bridgeVt_nsFree` = Unit C's landed conjunct at MovesU/BridgeD4_vtLaws):

* **Corpus census result (the blueprint's UNVERIFIED point (a), now checked):
  a clean machine-terminal "leaf ⇒ IrrHalts ∨ hen ∨ ns" lemma is ABSENT from
  the corpus.** What IS on record: `VTree.fiberAt`'s clause (2) — at a
  REALIZED tree, every maximal chain is booked τ-irr or τ-ns (exactly the
  case split `MovesT/E9_fiberDisjoint.lean` runs at its leaves); the τ-hen
  species books at the henV PAYLOAD (root events), never as a chain
  (`VTree.hne_nodes`) — the §9.2a inventory note. Per the fold-round-1
  ruling, `LeafCatalogue` therefore lands below as the NAMED HYPOTHESIS ROW,
  displayed clause list = the trichotomy with per-species seam faces, leaf
  pin = maximality in a realized (`fiberAt`-witnessed) tree — the ONE leaf
  notion on record at HEAD (the machine-side terminal home is C0's TRM,
  "purely owed"). At THIS pin the row is corpus-dischargeable
  (`leafCatalogue_of_fiberAt` below) — landed so the conditional theorem
  composes to an unconditional corollary; the row itself stays the displayed
  residue carrier. **Routed to the GD-4 owner brief (CUC §9.4 scope note):
  (i) whether the realized-chain pin is the right "leaf" inventory once C0's
  terminal read materializes, and (ii) the hen-species coverage at payload
  (non-chain) sites — the §9.2a inventory closure rides the same note.**
* **The bare A7 `tDECcor` row at SV is NOT claimed** (B1's honesty display
  extends to it): SV's `emitsHen` fires at EVERY reached k′ = 0 seam — the
  interface carries no terminal pin (C0 territory), so a reached-but-
  CONTINUING base state (a₀ ≥ 2, no −∞ side) would satisfy `emitsHen` while
  `DecHenSeam` fails. Per the B3a precedent, the packaged theorem carries
  the reach antecedent STRENGTHENED to a LEAF reach: the realizing history
  is additionally `HistLawful` (the Q1 fence, displayed — B3a's section
  header verbatim) and a MAXIMAL CHAIN of an `NsFree` realized tree (the
  leaf pin + the fence). The wired corollary `engineEmissionSV_tDECcor_bridge`
  consumes the fence conjunct from Unit C's landed `bridgeVt_nsFree`.
* **`DeepCorner` never reached, engine-strength**: two faces, both proved
  OUTRIGHT (no catalogue, no fence) — the emits leg concludes `DecSeam` with
  no corner disjunct (`engineEmissionSV_emits_decSeam`), and the corner is
  REFUTED at every emission site (`engineEmissionSV_deepCorner_never`: B1's
  `emits` carries `DecIrrSeam`, whose saturated last selection `some (g, 1)`
  contradicts the corner's `some (g, μ)`, `2 ≤ μ`). NO paper-machine claim
  rides here — whether the PAPER engine ever corner-books is explicitly
  GD-8 (blueprint §3.2(b), CUC §9.4).
* FOOTPRINT: everything binds `machineEHist` (certificate-free) — B0's
  footprint rule; all B3b rows Lean-core (verify at gate via `#print axioms`).
-/

/-- **H6-B3b, THE NAMED HYPOTHESIS ROW `LeafCatalogue (p F) : Prop`**
(blueprint §4 unit B3b, fold round 1 / Codex findings 9 + 13: the leaf
catalogue is PART OF THIS GROUP'S RESIDUE — a named row, never a sorry).
Displayed clause list — the leaf-species trichotomy "leaf ⇒ IrrHalts ∨
hen-booked ∨ ns-booked" at the one leaf pin on record at HEAD (maximality in
a realized tree; the machine-side terminal home is C0's TRM, owed):

for every realized (`fiberAt`-witnessed) tree `Tr` and every maximal chain
`M ∈ Tr.chains` that is a coherent classifier run on `f`,
* **(irr)** `MovesT.IrrHalts M` — the saturation booking; or
* **(hen)** M sits at the BASE (`M.nodes.tail = []`, the root-only history —
  k′ = 0 after the root-datum split) and every ι-certified read `D` of its
  dressed seam exhibits the booking datum: `a₀ = 1` (the Hensel branch) or a
  listed slope-−∞ side at level 0 (the j₀ = 1 exact-key branch) — the
  `DecHenSeam` face, D-relative exactly where the seam is; or
* **(ns)** `Tr.nsLeaf M` — the τ-ns mark, the leg the `NsFree` fence kills.

RESIDUE ROUTING (GD-4 owner brief, CUC §9.4 / §9.2a): the pin's adequacy once
C0's terminal read lands, and the hen-species coverage at payload (non-chain)
sites. Discharged at THIS pin by `leafCatalogue_of_fiberAt` below. -/
def LeafCatalogue (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ (n N m : ℕ) (pol : MovesD.CanonPolicy p F)
    (T : MovesD.TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (x : MovesD.Box p m) (Tr : MovesT.VTree p F)
    (f : Polynomial ℤ_[p]) (M : MovesC.History p F),
    Tr.fiberAt T χ x →
    M ∈ Tr.chains → MovesT.IsMaximalIn Tr.chains M →
    MovesC.HistoryCoherent M →
    LeanUrat.MovesJ.ReadsOf p F n f M →
    MovesT.IrrHalts M ∨
    (M.nodes.tail = [] ∧
      ∀ D : GMNData f (Theta ((machineEHist M).continuingPart)),
        ReadThroughIota f ((machineEHist M).continuingPart) D →
        ((machineEHist M).continuingPart.a0 = 1 ∨
          ∃ S ∈ D.principalSides 0, S.isNegInfty = true)) ∨
    Tr.nsLeaf M

/-- **H6-B3b — the row's corpus discharge at the realized-chain pin**: at a
`fiberAt` witness, clause (2) of `VTree.fiberAt` books every maximal chain
τ-irr or τ-ns (the exact case split of `MovesT/E9_fiberDisjoint.lean`'s leaf
leg) — the trichotomy holds with the hen clause never the witness (hen
bookings are henV PAYLOAD events, not chains — the §9.2a note in the section
header). The coherence/`ReadsOf` antecedents scope the row to engine-real
leaves; this discharge does not consume them. -/
theorem leafCatalogue_of_fiberAt (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : LeafCatalogue p F := by
  intro n N m pol T χ x Tr f M hfib hmem hmax _ _
  rcases hfib.2.1 M hmem hmax with h1 | h2
  · exact Or.inl h1.1
  · exact Or.inr (Or.inr h2.2.2.1)

/-- **H6-B3b — the emits leg, STRONG form (`DeepCorner` never entered)**: at
`engineEmissionSV` every verdict-carrying emission site is a DEC seam
outright — B1's `emits` body carries `DecIrrSeam H` as its second conjunct,
so `DecSeam` holds by the irr leg with NO corner disjunct consumed. -/
theorem engineEmissionSV_emits_decSeam (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F]
    (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
    (ν : ENodeData) (EF : ℕ × ℕ)
    (h : (engineEmissionSV n p F).emits f H ν EF) :
    DecSeam f H D :=
  Or.inl h.2.1

/-- **H6-B3b — `DeepCorner` NEVER REACHED at the engine emission**
(ENGINE-strength only — no paper-machine claim, blueprint §3.2(b)): the deep
exact-key corner is REFUTED at every `engineEmissionSV` emission site — the
emitted seam's decided last selection is saturated (`sel = some (g, 1)`,
B1's `DecIrrSeam` conjunct) while the corner demands an exact key
`sel = some (g, μ)` with `2 ≤ μ` at the SAME last node. -/
theorem engineEmissionSV_deepCorner_never (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F]
    (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
    (ν : ENodeData) (EF : ℕ × ℕ)
    (h : (engineEmissionSV n p F).emits f H ν EF) :
    ¬ DeepCorner f H D := by
  rintro ⟨-, hsel, -⟩
  obtain ⟨-, hdec, -, -⟩ := h
  obtain ⟨-, hlast⟩ := hdec
  cases hL : H.nodes.getLast? with
  | none => rw [hL] at hlast; exact hlast
  | some ν₀ =>
    rw [hL] at hlast hsel
    simp only [Option.elim_some] at hlast hsel
    obtain ⟨g, hg⟩ := hlast
    obtain ⟨g', μ', hg', hμ⟩ := hsel
    rw [hg, Option.some.injEq, Prod.mk.injEq] at hg'
    omega

/-- **H6-B3b, PACKAGED: (T-DEC-cor) at the engine** — the A7 `tDECcor` row
shape at `E := engineEmissionSV n p F`, both legs, CONDITIONAL on the named
row `LeafCatalogue p F` (the fold-round-1 / Codex finding 9 form) and with
the row's implicit reach antecedent STRENGTHENED to a LEAF reach (the B3a
precedent; the bare-row form is NOT claimed — see the section header): the
realizing history is additionally `HistLawful` (the Q1 fence, explicit) and a
maximal chain of an `NsFree` realized tree (the leaf pin + the ns fence).

Route: the emits leg is the strong-form lemma (`DecSeam`, corner never
entered). The hen leg runs the blueprint's chain verbatim — the catalogue's
trichotomy at the leaf witness, with (irr) ⇒ `a₀ = 1` via
`MovesT.irr_iff_mu_one` at the root read (the 1-node corner B3a splits off:
here it IS the hen channel, `machineEHist_a0` transports `root.μ` to the
seam's `a₀`), (hen) ⇒ the `DecHenSeam` face directly, and (ns) killed by the
`NsFree` fence conjunct. -/
theorem engineEmissionSV_tDECcor (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F]
    (hcat : LeafCatalogue p F) :
    ∀ (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
      (R : GMNReader f (Theta H) D),
      ReadThroughIota f H D → ConsF f H D R →
      (∃ (N m : ℕ) (pol : MovesD.CanonPolicy p F)
        (T : MovesD.TreeModel p F n N m pol) (χ : Fin n → Fin m)
        (x : MovesD.Box p m) (Tr : MovesT.VTree p F)
        (M : MovesC.History p F),
        Tr.fiberAt T χ x ∧
        M ∈ Tr.chains ∧ MovesT.IsMaximalIn Tr.chains M ∧
        MovesT.NsFree Tr ∧
        MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        MovesT.HistLawful p n M ∧
        (machineEHist M).continuingPart = H) →
      (∀ ν EF, (engineEmissionSV n p F).emits f H ν EF →
        DecSeam f H D ∨ DeepCorner f H D) ∧
      (∀ EF, (engineEmissionSV n p F).emitsHen f H EF → DecHenSeam f H D) := by
  intro f H D R hiota hcons hleaf
  obtain ⟨N, m, pol, T, χ, x, Tr, M, hfib, hmem, hmax, hnsf, hcoh, hread,
    hlaw, hpart⟩ := hleaf
  subst hpart
  refine ⟨fun ν EF h => Or.inl (engineEmissionSV_emits_decSeam n p F f _ D ν EF h),
    fun EF hE => ?_⟩
  obtain ⟨hnil, -, -⟩ := hE
  refine ⟨hnil, ?_⟩
  rcases hcat n N m pol T χ x Tr f M hfib hmem hmax hcoh hread with
    hirr | ⟨-, hhen⟩ | hns
  · -- (irr) at the base: the root read saturates, a₀ = 1 — the Hensel branch.
    left
    have htail : M.nodes.tail = [] := by
      have h1 := hnil
      rw [machineEHist_continuingPart_nodes] at h1
      exact List.map_eq_nil_iff.mp h1
    obtain ⟨a, t, hM⟩ := List.exists_cons_of_ne_nil M.nonempty
    have ht : t = [] := by rw [hM] at htail; exact htail
    subst ht
    have hlast : M.nodes.getLast? = some a := by rw [hM]; rfl
    have hmu : a.μ = 1 := (MovesT.irr_iff_mu_one M n hlaw a hlast).mp hirr
    rw [machineEHist_continuingPart, machineEHist_a0]
    simp only [hM, List.head_cons]
    exact hmu
  · -- (hen) the booking datum is the `DecHenSeam` face, read off at our D.
    exact hhen D hiota
  · -- (ns) fenced: the tree carries no ns mark.
    exact absurd hns (hnsf M hmem)

/-- **H6-B3b — the wired corollary at Unit C's landed fence**: the packaged
(T-DEC-cor) row with the `NsFree` conjunct DISCHARGED by `bridgeVt_nsFree`
(the (NSF-KEY) repair conjunct on the `bridgeTree` carrier — "Unit C's landed
`bridgeTree` conjunct", blueprint §4 B3b verbatim): a leaf reach on a CARRIED
σ-tree needs no separate fence hypothesis. F = ZMod p is the carrier's own
residue world (`bridgeVt : bridgeTree n p σ → MovesT.VTree p (ZMod p)`). -/
theorem engineEmissionSV_tDECcor_bridge (n p : ℕ) [Fact p.Prime]
    (hcat : LeafCatalogue p (ZMod p)) :
    ∀ (f : Polynomial ℤ_[p]) (H : EHist p (ZMod p))
      (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
      ReadThroughIota f H D → ConsF f H D R →
      (∃ (N m : ℕ) (pol : MovesD.CanonPolicy p (ZMod p))
        (T : MovesD.TreeModel p (ZMod p) n N m pol) (χ : Fin n → Fin m)
        (x : MovesD.Box p m) (σ : LeanUrat.MovesU.SplittingType n)
        (Tb : LeanUrat.MovesU.bridgeTree n p σ)
        (M : MovesC.History p (ZMod p)),
        (LeanUrat.MovesU.bridgeVt n p σ Tb).fiberAt T χ x ∧
        M ∈ (LeanUrat.MovesU.bridgeVt n p σ Tb).chains ∧
        MovesT.IsMaximalIn (LeanUrat.MovesU.bridgeVt n p σ Tb).chains M ∧
        MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p (ZMod p) n f M ∧
        MovesT.HistLawful p n M ∧
        (machineEHist M).continuingPart = H) →
      (∀ ν EF, (engineEmissionSV n p (ZMod p)).emits f H ν EF →
        DecSeam f H D ∨ DeepCorner f H D) ∧
      (∀ EF, (engineEmissionSV n p (ZMod p)).emitsHen f H EF →
        DecHenSeam f H D) := by
  intro f H D R hiota hcons hleaf
  obtain ⟨N, m, pol, T, χ, x, σ, Tb, M, hfib, hmem, hmax, hcoh, hread,
    hlaw, hpart⟩ := hleaf
  exact engineEmissionSV_tDECcor n p (ZMod p) hcat f H D R hiota hcons
    ⟨N, m, pol, T, χ, x, LeanUrat.MovesU.bridgeVt n p σ Tb, M, hfib, hmem,
      hmax, LeanUrat.MovesU.bridgeVt_nsFree n p σ Tb, hcoh, hread, hlaw, hpart⟩

end LeanUrat.Scaffold.HDischarge.H6
