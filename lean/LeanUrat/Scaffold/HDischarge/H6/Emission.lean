/-
HDISCHARGE_H6 §4 Wave A — `H6/Emission.lean`: E-side accumulators (unit A1, MECH).
Statement transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 A1
(probe-verified 2026-08-05). Cures defect D-6 (the architect-ruling proposal the
III-H9 BLOCKED block requested); also the answer to `DictIII/CU2t.lean`'s
BLOCKED(III-S2)/(III-S3) records, which hit the same accE/accF carrier seam
(BP_III wave-5 resume record defers that mop-up to this lead).

Reading: `eAccE H = ∏ ν.e` over the node list; `eAccF H = f₀ · ∏ (sel g's)`
with f₀ := deg ψ̂₀ (the root residue factor) and each selection-carrying node
contributing its g (terminal `sel = none` contributes 1 via `Option.elim`).
Gate (CUC §9.2 k′ = 0 boundary): at `H.nodes = []` the pair reduces to
`(accE₀, accF₀) = (1, f₀)` by `simp` — the `example` below.

Definitional risk on record (blueprint §3.4, fold round 1 Codex finding 12):
the reconciliation of this f₀-included `eAccF` with the machine's
`accF = ∏ ν.g` through the root-datum split is unit B2's content, NOT assumed
here.
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU2t
import LeanUrat.MovesU.DefsLedger
import LeanUrat.Moves.Defs

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII
open LeanUrat.MovesU

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- H6-A1 — E-side ramification accumulator: `accE_{k′} = ∏_{ν ∈ nodes} ν.e`. -/
def eAccE (H : EHist p F) : ℕ := (H.nodes.map fun ν => ν.e).prod

/-- H6-A1 — E-side residue-degree accumulator:
`accF_{k′} = f₀ · ∏_{ν ∈ nodes} (sel g)`, f₀-included form (CUC §9.2). -/
def eAccF (H : EHist p F) : ℕ :=
  H.psi0.natDegree * (H.nodes.map fun ν => (ν.sel.elim 1 Prod.fst)).prod

/-- A1 gate: the CUC §9.2 k′ = 0 boundary `(accE₀, accF₀) = (1, f₀)`. -/
example (H : EHist p F) (h : H.nodes = []) :
    (eAccE H, eAccF H) = (1, H.psi0.natDegree) := by
  simp [eAccE, eAccF, h]

/-! ## Unit A2 — seam decidedness, repaired (cures D-7/D-8)

Statements transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 A2
(probe-verified 2026-08-05). NEW names alongside the landed `DecIrr`/`DecHen`
pair in `DictIII/CU2t.lean` — the fenced pair is UNTOUCHED.

Reading (displayed at A2): `H` is 𝐇° (the seam continuing part; all nodes
selection-carrying — enforced at consumption via
`TerminalEmission.reaches_continuing`, unit A6). -/

/-- H6-A2 — seam decidedness, τ-irr leg: 𝐇° is nonempty and its last node
carries a saturated selection `sel = some (g, 1)` (μ_last = 1). Repaired NEW
name alongside the landed `DecIrr` (cures D-7). -/
def DecIrrSeam (H : EHist p F) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g, ν.sel = some (g, 1))

/-- H6-A2 — seam decidedness, τ-hen leg: the base read — 𝐇° has no nodes, and
either `a₀ = 1` (Hensel booking) or the level-0 read has a slope-−∞ side.
Repaired NEW name alongside the landed `DecHen` (cures D-8). -/
def DecHenSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes = [] ∧
    (H.a0 = 1 ∨ ∃ S ∈ D.principalSides 0, S.isNegInfty = true)

/-- H6-A2 — seam decidedness, disjunction: a DEC seam is a τ-irr or a τ-hen
configuration. -/
def DecSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  DecIrrSeam H ∨ DecHenSeam f H D

/-- H6-A3 — the deep exact-key corner (CUC §9.4 (T-DEC-cor) shape): the seam is
nonempty, its last node carries an exact selection key `some (g, μ)` with `2 ≤ μ`,
and the polygon read at index `H.nodes.length` exhibits a slope-−∞ side.

LEVEL CONVENTION (displayed, per blueprint §4 A3): `D.principalSides i` at
0-indexed `i` = the paper's level-(i+1) read; `H.nodes.length = k′` ⇒ index `k′`
= level `k′+1` — the same convention as BP_III §1.9's `cu2t_readForcing`. -/
def DeepCorner (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g μ, ν.sel = some (g, μ) ∧ 2 ≤ μ) ∧
    ∃ S ∈ D.principalSides H.nodes.length, S.isNegInfty = true

/-! ## Unit A4 — the forced terminal datum, repaired (cures D-5/D-6)

Statements transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 A4
(probe-verified 2026-08-05). Deps: A1 (`eAccE`/`eAccF`), A2 (`DecIrrSeam`).

`head?` is junk-tolerant: on a junk `D` (e.g. `principalSides ≡ []`) the slope
is `none` and nothing downstream fires. On DEC seams the side is forced UNIQUE —
that forcing lemma (III-S4) remains BP_III's unit and is NOT re-owned here; the
coherence of this `head?`-read with `RCConsistentD`'s ∀-form clause is unit
A4b's DISPLAYED obligation (`terminalDatumD_slope_spec`, lands once III-S4
lands) — assumed nowhere in this file. -/

/-- H6-A4 — the forced terminal datum: the `head?`-read slope pair (with the
slope-−∞ side mapped to `none`) + the emission verdict pair. -/
structure TerminalDatumD where
  slope : Option (ℕ × ℕ)
  verdict : ℕ × ℕ

open scoped Classical in
/-- H6-A4 — the forced terminal datum, repaired (cures D-5/D-6): `slope` is the
junk-tolerant `head?` read of the polygon sides at index `H.nodes.length`
(= paper level k′+1, the A3 convention); `verdict` books `(eAccE, eAccF)` on a
τ-irr DEC seam and the base pair `(1, f₀)` otherwise. -/
noncomputable def terminalDatumD (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : TerminalDatumD :=
  { slope := (D.principalSides H.nodes.length).head?.bind fun S =>
      if S.isNegInfty then none else some (S.e, S.h)
    verdict := if DecIrrSeam H then (eAccE H, eAccF H) else (1, H.psi0.natDegree) }

/-- H6-A6 (VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit A6): the
terminal-emission interface — the quantifier domain the CUC §9.4 rows need and
the BP_III display lacked (the root cause of defects D-1..D-4).

`emitsHen` = the verdict-pair-only machine-record booking channel — the fold
round 1 repair of Codex finding 1; see HDISCHARGE_H6 §3.1. -/
structure TerminalEmission (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] where
  reaches : Polynomial ℤ_[p] → EHist p F → Prop
  emits : Polynomial ℤ_[p] → EHist p F → ENodeData → (ℕ × ℕ) → Prop
  emitsHen : Polynomial ℤ_[p] → EHist p F → (ℕ × ℕ) → Prop
  emits_terminal : ∀ f H ν EF, emits f H ν EF → ν.sel = none
  emits_reaches : ∀ f H ν EF, emits f H ν EF → reaches f H
  emitsHen_reaches : ∀ f H EF, emitsHen f H EF → reaches f H
  reaches_continuing : ∀ f H, reaches f H → ∀ ν ∈ H.nodes, ν.sel ≠ none

/-! ## Unit A6b — `ReadThroughIota`, the GMN-through-ι certificate (PINNED SIGNATURE)

Signature transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit
A6b (`def ReadThroughIota (f : Polynomial ℤ_[p]) (H : EHist p F)
(D : GMNData f (Theta H)) : Prop`); the BODY is this unit's E-phase duty under
the §4 C0-style constraints (observable content pinned, rendering free).  The
certificate is the fold-round-1 repair of Codex finding 2: without it every
∀-D row of A7 is refutable at a lawless `GMNData` (empty side lists make
trivial `DecHenSeam` witnesses and refute universal-D `tDECcor`).

PINNED CONTENT (blueprint §4 A6b): D's side lists at levels 0..k′
(k′ = `H.nodes.length`) are the REAL polygon reads of f over Θ(𝐇°) through ι —
* **level 0 (Lean index 0 = paper level 1), CORPUS-REAL, no freedom**: the
  corpus base Newton polygon w.r.t. the ψ̂₀-key, i.e. `principalData f` —
  EXACTLY the level-0 value of `DictIII/O2aOrder1.lean`'s constructor
  `gmnDataOrder1` (`OM/` polygon API: `npSides` over `M2.valSupport`).
  Rendering: clause (i) pins the FINITE-slope entries to `principalData f`
  by filter-equality, and clause (ii) permits a slope-−∞ entry ONLY when the
  −∞ side is real (`f.coeff 0 = 0`, i.e. the corpus base read's abscissa-0
  slot vanishes).  Plain list-equality would be UNFAITHFUL both ways: the
  corpus polygon API carries finite sides only (the III-A6a scope note — the
  GMN Def 1.1 slope-−∞ side has no `npSides` representative), so equality
  would falsify the certificate at the honest real read whenever `j₀ ≥ 1`,
  AND it would make `DecHenSeam`'s −∞ branch unsatisfiable under
  certification — silently killing a live CUC case (§3.3(a)'s j₀ = 1 branch).
  The III-A6a ψ̂₀-key scope caveat (the corpus base read is the coefficient
  polygon; abscissae are X-powers) rides this clause unchanged.
* **levels ≥ 1 (Lean index i+1 = paper level i+2), OL-1-CONDITIONAL** (the
  CUC (c1) bracket verbatim: "level 1 unconditional, levels ≥ 2 given
  OL-1"): clause (iii) demands, for EVERY lift granted by the named row
  `OL1 (Theta H)`, that every listed side at level i+1 conforms to the real
  φ-adic development of f w.r.t. the OL-1-certified key
  `lift i ((Theta H).psihat i)`.  KEY CONVENTION (displayed): Lean
  `psihat i` = paper ψ̂_{i+1} (the `EWF_dress`/`w4dress` indexing), and the
  paper level-(i+2) read key is φ_{i+2} = Lift(ψ̂_{i+1}); `OL1`'s in-range
  grant `i < (Theta H).slopes.length` covers EXACTLY the read levels
  1..k′ on a continuing 𝐇° — no off-range junk dressing is consumed.
  HONESTY (this face is priced as group residue, fold-round-1 record): the
  clauses are the CORPUS-STATABLE face of "is the real level-(i+2) read" —
  a finite side's abscissa span `[s, s + e·ℓ]` has genuine nonzero
  development slots at both endpoints, and a slope-−∞ entry forces the
  0-slot to vanish (key divides f).  The ORDINATE face (slopes/heights
  through the level-i MacLane weight w_i) is NOT statable at HEAD — that is
  exactly the OL-1/GRB (H1-group) residue, NOT discharged and NOT weakened
  into a `True` placeholder here; consumers get the full "real read through
  ι" strength only together with the OL rows, as the CUC prices it.

GATES (landed WITH the unit, per the pinning demands):
* positive — `readThroughIota_order1_gate`: the canonical order-≤1 `GMNData`
  (`gmnDataOrder1`, the ONLY corpus-real constructor at HEAD) satisfies the
  certificate for EVERY f and H in its perimeter; instantiated concretely at
  the III-A9 gate world by `readThroughIota_order1_gate_pos` (p = 2,
  F = ZMod 2, f = X, the one-node `ol6GateHist`) — non-vacuous.
* negative — `readThroughIota_lawless_fails`: the lawless
  `⟨fun _ => [], fun _ => 0, fun _ => 0, 0⟩` FAILS the certificate at the
  compiled witness f = X + 2 over ℤ_[2] (whose corpus base polygon is the
  single side (0,1)–(1,0) of slope −1: `principalData_X_add_two`).

Consumption: every A7 row takes `ReadThroughIota f H D` + `ConsF f H D R` as
standing antecedents (the CUC hypotheses "Cons_f(𝐇°)" + "GMN objects through
ι" transcribed).  Non-circularity: D is polygon data of f over Θ(𝐇°); no
clause mentions the true factor.  Field-inventory closure beyond the side
lists (residual orders/degrees, root order) is GD-4-owner territory (the §9.2a
caveat at A5) — deliberately NOT pinned here. -/

/-- H6-A6b (SIGNATURE VERBATIM, `lean/blueprints/HDISCHARGE_H6.md` §4 unit
A6b): the GMN-through-ι certificate.  Clause (i): the finite-slope entries at
level 0 are EXACTLY the corpus base Newton polygon read `principalData f`
(corpus-real, no freedom).  Clause (ii): a slope-−∞ entry at level 0 only when
the −∞ side is real (`f.coeff 0 = 0`).  Clause (iii), the OL-1-conditional
face (group residue, displayed in the section header): for every `OL1`-granted
lift, every side listed at level i+1 (i < k′) conforms to the real φ-adic
development of f w.r.t. the certified key `lift i (ψ̂_{i+1})` — finite sides
anchor both abscissa endpoints on nonzero development slots; −∞ entries force
the 0-slot to vanish. -/
def ReadThroughIota (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  (D.principalSides 0).filter (fun S => !S.isNegInfty) = principalData f ∧
  (∀ S ∈ D.principalSides 0, S.isNegInfty = true → f.coeff 0 = 0) ∧
  (∀ lift : LiftFn p F, OL1 (Theta H) lift →
    ∀ i, i < H.nodes.length →
      ∀ B N, LeanUrat.Moves.IsDevelopment (lift i ((Theta H).psihat i)) f B N →
        ∀ S ∈ D.principalSides (i + 1),
          (S.isNegInfty = false → B S.s ≠ 0 ∧ B (S.s + S.e * S.ℓ) ≠ 0) ∧
          (S.isNegInfty = true → B 0 = 0))

/-- A6b POSITIVE GATE, general form: the canonical order-≤1 `GMNData`
(`gmnDataOrder1` — the corpus polygon constructor, unit III-A6a) satisfies the
certificate for every `f`, `H`, ι-parameters, and order-≤1 perimeter witness.
Clause (i) is the constructor's own level-0 value (every constructed datum is
finite-slope, `mem_principalData`); clause (ii) is vacuous on finite-slope
data; clause (iii) is vacuous at the constructor's empty deep levels. -/
theorem readThroughIota_order1_gate (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ιb : ZMod p →+* ↥(Theta H).base) (ι0 : ZMod p →+* ↥((Theta H).fld 0))
    (hlen : (Theta H).slopes.length ≤ 1) :
    ReadThroughIota f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen) := by
  refine ⟨?_, ?_, ?_⟩
  · have h0 : (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides 0
        = principalData f := by
      simp [gmnDataOrder1]
    rw [h0]
    refine List.filter_eq_self.mpr fun T hT => ?_
    obtain ⟨S, -, -, rfl⟩ := mem_principalData hT
    rfl
  · intro S hS htrue
    have h0 : (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides 0
        = principalData f := by
      simp [gmnDataOrder1]
    rw [h0] at hS
    obtain ⟨S', -, -, rfl⟩ := mem_principalData hS
    simp [sideToDatum] at htrue
  · intro lift _ i _ B N _ S hS
    have h1 : (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides (i + 1)
        = [] := by
      simp [gmnDataOrder1]
    rw [h1] at hS
    exact absurd hS (List.not_mem_nil)

/-- The ι-parameter at the III-A9 gate world: `ZMod 2` into the top subfield of
`ZMod 2` (both the base and every tower level of `ol6GateHist` are `⊤`). -/
noncomputable def gateIota : ZMod 2 →+* ↥(⊤ : Subfield (ZMod 2)) :=
  Subfield.topEquiv.symm.toRingHom

/-- A6b POSITIVE GATE, concrete instance (non-vacuity): the canonical order-≤1
datum over the III-A9 one-node gate world (p = 2, F = ZMod 2, f = X,
`ol6GateHist` with its single continuing node) IS certified. -/
theorem readThroughIota_order1_gate_pos :
    ReadThroughIota (Polynomial.X : Polynomial ℤ_[2]) ol6GateHist
      (gmnDataOrder1 (Polynomial.X : Polynomial ℤ_[2]) (Theta ol6GateHist)
        gateIota gateIota ol6Gate_slopes_length.le) :=
  readThroughIota_order1_gate _ _ _ _ _

/-! ### A6b NEGATIVE GATE — the lawless datum fails at a compiled polygon

Witness: f = X + 2 over ℤ_[2].  Its valuation support is {(0,1), (1,0)}
(v(2) = 1, v(1) = 0), whose lower hull is the single chord (0,1)–(1,0) of
slope −1 < 0 — so the corpus principal read `principalData f` is the singleton
`[(1,1,1,0,1)]` and clause (i) refutes the empty-side-list datum.  The hull
computation follows the `npVertices_zeroPair` template (`OM/NewtonPolygon`),
with the chord as the valid supporting line. -/

/-- The negative-gate support: the valuation support of X + 2 over ℤ_[2]. -/
private def negGateSupport : Finset (ℕ × ℕ) := {(0, 1), (1, 0)}

private lemma negGateSupport_nonempty : negGateSupport.Nonempty :=
  ⟨(0, 1), by simp [negGateSupport]⟩

open LeanUrat.OM in
/-- The chord (0,1)–(1,0) is a valid supporting line of the negative-gate
support. -/
private lemma negGate_chord_valid :
    (((0, 1), (1, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ NewtonPolygon.validLines negGateSupport := by
  classical
  -- (`OM/NewtonPolygon` builds its filters under scoped `Classical`)
  rw [NewtonPolygon.validLines, Finset.mem_filter]
  refine ⟨Finset.mem_product.2 ⟨by simp [negGateSupport], by simp [negGateSupport]⟩, ?_⟩
  intro Q hQ
  rw [negGateSupport, Finset.mem_insert, Finset.mem_singleton] at hQ
  rcases hQ with rfl | rfl <;>
    norm_num [NewtonPolygon.pairLine, NewtonPolygon.pairSlope]

open LeanUrat.OM in
private lemma negGate_npHeight_zero :
    NewtonPolygon.npHeight negGateSupport negGateSupport_nonempty ((0 : ℕ) : ℚ)
      = 1 := by
  refine le_antisymm ?_ ?_
  · have := NewtonPolygon.npHeight_le negGateSupport negGateSupport_nonempty
      (i := 0) (v := 1) (by simp [negGateSupport])
    simpa using this
  · have hle := Finset.le_sup'
      (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => NewtonPolygon.pairLine PR.1 PR.2 ((0 : ℕ) : ℚ))
      negGate_chord_valid
    refine le_trans (le_of_eq ?_) hle
    norm_num [NewtonPolygon.pairLine, NewtonPolygon.pairSlope]

open LeanUrat.OM in
private lemma negGate_npHeight_one :
    NewtonPolygon.npHeight negGateSupport negGateSupport_nonempty ((1 : ℕ) : ℚ)
      = 0 := by
  refine le_antisymm ?_ ?_
  · have := NewtonPolygon.npHeight_le negGateSupport negGateSupport_nonempty
      (i := 1) (v := 0) (by simp [negGateSupport])
    simpa using this
  · have hle := Finset.le_sup'
      (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => NewtonPolygon.pairLine PR.1 PR.2 ((1 : ℕ) : ℚ))
      negGate_chord_valid
    refine le_trans (le_of_eq ?_) hle
    norm_num [NewtonPolygon.pairLine, NewtonPolygon.pairSlope]

open LeanUrat.OM in
/-- The negative-gate hull: both support dots are on the hull, the vertex list
is the full chord. -/
private lemma negGate_npVertices :
    NewtonPolygon.npVertices negGateSupport negGateSupport_nonempty
      = [(0, 1), (1, 0)] := by
  have hdots : NewtonPolygon.hullDots negGateSupport negGateSupport_nonempty
      = negGateSupport := by
    classical
    -- (`OM/NewtonPolygon` builds its filters under scoped `Classical`)
    rw [NewtonPolygon.hullDots]
    refine Finset.filter_true_of_mem fun P hP => ?_
    rw [negGateSupport, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · change ((1 : ℕ) : ℚ) = _
      rw [negGate_npHeight_zero]; norm_num
    · change ((0 : ℕ) : ℚ) = _
      rw [negGate_npHeight_one]; norm_num
  have himg : negGateSupport.image Prod.fst = {0, 1} := by decide
  have hsort : ({(0 : ℕ), (1 : ℕ)} : Finset ℕ).sort (· ≤ ·) = [0, 1] := by
    have h1 : ∀ b ∈ ({(1 : ℕ)} : Finset ℕ), 0 ≤ b := fun b _ => Nat.zero_le b
    have h2 : (0 : ℕ) ∉ ({(1 : ℕ)} : Finset ℕ) := by decide
    rw [Finset.sort_insert (fun x1 x2 : ℕ => x1 ≤ x2) h1 h2, Finset.sort_singleton]
  have hd0 : NewtonPolygon.hullDotAt negGateSupport negGateSupport_nonempty 0
      = (0, 1) := by
    unfold NewtonPolygon.hullDotAt NewtonPolygon.hullHeightAt
    rw [show ((0 : ℕ) : ℚ) = ((0 : ℕ) : ℚ) from rfl, negGate_npHeight_zero]
    norm_num
  have hd1 : NewtonPolygon.hullDotAt negGateSupport negGateSupport_nonempty 1
      = (1, 0) := by
    unfold NewtonPolygon.hullDotAt NewtonPolygon.hullHeightAt
    rw [negGate_npHeight_one]
    norm_num
  unfold NewtonPolygon.npVertices NewtonPolygon.npVerticesFull
    NewtonPolygon.hullAbscissae
  rw [hdots, himg, hsort, List.map_cons, List.map_cons, List.map_nil, hd0, hd1]
  rfl

open LeanUrat.OM in
/-- The negative-gate side list: the single chord side (0,1)–(1,0). -/
private lemma negGate_npSides :
    NewtonPolygon.npSides negGateSupport negGateSupport_nonempty
      = [⟨0, 1, 1, 0⟩] := by
  rw [NewtonPolygon.npSides, negGate_npVertices]
  rfl

open LeanUrat.OM in
/-- The valuation support of X + 2 over ℤ_[2] is the negative-gate support:
v(2) = 1 at abscissa 0, v(1) = 0 at abscissa 1. -/
private lemma negGate_valSupport :
    M2.valSupport 2 (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2])
      = negGateSupport := by
  have h2 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  have hv2 : (2 : ℤ_[2]).valuation = 1 := by
    simpa using PadicInt.valuation_p (p := 2)
  have hc0 : (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2]).coeff 0 = 2 := by
    simp
  have hc1 : (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2]).coeff 1 = 1 := by
    simp
  have hchar := (M2.valSupport_facts 2
    (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2])).1
  ext ⟨i, v⟩
  rw [hchar i v, negGateSupport, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, rfl⟩
    match i with
    | 0 =>
        left
        rw [Prod.mk.injEq]
        exact ⟨rfl, by rw [M2.coeffVal, hc0, hv2]⟩
    | 1 =>
        right
        rw [Prod.mk.injEq]
        exact ⟨rfl, by rw [M2.coeffVal, hc1, PadicInt.valuation_one]⟩
    | (n + 2) =>
        exfalso
        apply hne
        simp [Polynomial.coeff_X]
  · rintro (h | h) <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · exact ⟨by rw [hc0]; exact h2, by rw [M2.coeffVal, hc0, hv2]⟩
    · exact ⟨by rw [hc1]; exact one_ne_zero,
        by rw [M2.coeffVal, hc1, PadicInt.valuation_one]⟩

open LeanUrat.OM in
/-- The compiled corpus base read of the negative-gate witness: ONE principal
side, the (c1)-datum (e, h, ℓ, s, u) = (1, 1, 1, 0, 1) of the slope-−1 chord. -/
theorem principalData_X_add_two :
    principalData (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2])
      = [sideToDatum ⟨0, 1, 1, 0⟩] := by
  have hne : (M2.valSupport 2
      (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2])).Nonempty := by
    rw [negGate_valSupport]; exact negGateSupport_nonempty
  have hsl : sideList (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2])
      = [⟨0, 1, 1, 0⟩] := by
    rw [sideList, dif_pos hne,
      NewtonPolygon.npSides_congr _ negGateSupport hne negGateSupport_nonempty
        negGate_valSupport,
      negGate_npSides]
  have hside : (⟨0, 1, 1, 0⟩ : NewtonPolygon.Side).h = -1 := by
    have hs : (⟨0, 1, 1, 0⟩ : NewtonPolygon.Side).slope = -1 := by
      norm_num [NewtonPolygon.Side.slope]
    rw [NewtonPolygon.Side.h, hs]
    norm_num
  rw [principalData, principalSideList, hsl]
  simp [hside]

/-- A6b NEGATIVE GATE: the lawless `GMNData` `⟨fun _ => [], fun _ => 0,
fun _ => 0, 0⟩` (the blueprint's displayed refuter of the pre-repair A7 rows)
FAILS `ReadThroughIota` at the compiled witness f = X + 2 over ℤ_[2] — its
empty level-0 list cannot be the real corpus read, which has one side. -/
theorem readThroughIota_lawless_fails :
    ¬ ReadThroughIota (Polynomial.X + Polynomial.C 2 : Polynomial ℤ_[2])
        ol6GateHist ⟨fun _ => [], fun _ => 0, fun _ => 0, 0⟩ := by
  rintro ⟨h0, -, -⟩
  rw [show (GMNData.principalSides ⟨fun _ => [], fun _ => 0, fun _ => 0, 0⟩ 0
      : List SideDatum) = [] from rfl,
    List.filter_nil, principalData_X_add_two] at h0
  exact List.cons_ne_nil _ _ h0.symm

end LeanUrat.Scaffold.HDischarge.H6
