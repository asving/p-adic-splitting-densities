/-
HDISCHARGE_H6 §4 Wave C — `H6/TerminalRead.lean`: unit C0 (HARD, design-first).
TRM — the terminal-read materialization at the machine leaf (the machine-side
home CUC §9.4 calls "purely owed").

OBSERVABLE I/O PINNED at `lean/blueprints/HDISCHARGE_H6.md` §4 unit C0 (fold
round 1, Codex finding 11 — transcribed verbatim): inputs =
`(M : MovesC.History p F)` (the leaf's machine history) +
`(hM : HistoryCoherent M)` + `(hR : LeanUrat.MovesJ.ReadsOf p F n f M)` + `f`
itself — **NO GMNData input** (the record must be READ FROM f's development in
the terminal frame, not copied from semantic data); output = `ν : ENodeData`
with `ν.sel = none`; demanded theorems = (spec-1) `SideReads`-style
conformance of ν's (e, h, ℓ, s, u) to f's development in frame
`M.nodes.length` (the corpus `IsDevelopment` + side-read vocabulary at the
terminal index, no successor key), and (spec-2) the emission tie:
`engineEmission`'s emits holds exactly at (ν = terminalReadRecord …) —
upgrading B1's SV body; `EngineTied` re-proof rides along.  Implementation
only is free.

DESIGN RECORD (C0 is design-first; the choices, with provenance):

* **The terminal frame** (frame `M.nodes.length` = paper level k′+1, the A3
  convention transposed to the machine index chain: machine node i reads at
  paper level i, E-node i−1): its KEY is the last read's landing key —
  `MovesC.LandingKey (M.nodes.getLast M.nonempty) Φterm`, exactly the clause
  `ReadsOf` designates existentially at the final read ("the designated final
  key stays existential at the last read", HC2/Defs D4 fold note).  Its
  COEFFICIENT WEIGHT is machine-statable through the child-stage stretch law
  (Moves/Defs `Stage.hStretch`, DEF-4: `w B = e·wPrev B` on `C_Φ`) at the
  terminal frame, whose scale factor is the LAST READ's `e` and whose parent
  weight is the last frame's recorded `σ.w` — `termCoeffW` below.  This is
  the ONLY frame-(k′+1) valuation datum on machine record (no `Stage` exists
  at the terminal index; that absence is exactly why CUC §9.4 prices this
  home as "purely owed").
* **The conformance vocabulary** (`TerminalSideReads`): `SideReads`' clauses
  (i) SIDE + (ii) DIGITS transposed to the (e, h, ℓ, s, u) datum granularity
  of a TERMINAL record (`ENodeData`, `sel = none` — no `pat`, no anchor, no
  successor key: clauses (iii)–(vi) have no terminal analogue at HEAD).  The
  record's total side weight is recovered as `γ = e·u + s·h` — the exact
  inversion of `nodeToE`'s `u := (gam − s0·h)/e` (CU1 III-U1), so (s, u) is
  the side's INITIAL point, the (c1) positional clause's reading.
* **The −∞ branch**: `ENodeData` carries no slope-−∞ marker, so the j₀ = 1
  sub-case (CUC §9.2: the slope-−∞ side, length 1) is carried as the
  development fact `B 0 = 0` (the key divides f) — EXACTLY the clause A6b's
  certificate demands of a listed −∞ side (`S.isNegInfty = true → B 0 = 0`),
  so the C1/C2 bridging meets this branch on shared vocabulary.  The −∞
  branch pins NO shape fields: that granularity is the §9.2a datum-inventory
  caveat (GD-4-owner territory), displayed, not silently resolved.
* **The implementation** (free per the pin): choice-on-spec — the classically
  chosen conformant record when one exists, else a junk sel-none record.
  This is the RATIFIED corpus pattern (HC2/Defs `polOM`: "the classically
  chosen realizer of `RecenterLiftSpec` when one exists, else 0").
* **HONEST RESIDUE (spec-1's conditionality, displayed — nothing discharged
  by fiat):** conformant-record EXISTENCE at a genuine DEC seam is Lemma
  CU-2t 9.1(i) mathematics (the unique length-1 side of N_{k′+1}⁻(f); needs
  the perimeter disc f ≠ 0 and the seam hypotheses — NOT consequences of
  `ReadsOf` alone), so the unconditional form of spec-1 is FALSE at junk
  (f, M) and the faithful statement is conditional on the NAMED residue
  `TerminalReadExists f M` below.  Its discharge is exactly C1's PROVE door
  (k′ = 0) and the OL-row-conditional k′ ≥ 1 leg (§3.3) — this group's
  priced residue, assumed nowhere in this file.

Deps: B1 (`engineEmissionSV`, `EngineTied` — H6/EngineConform); A2/A6
(`DecIrrSeam`, `TerminalEmission` — H6/Emission); corpus `machineEHist` (CU1),
`MovesJ.ReadsOf`/`SideReads` (HC2/Defs), `MovesC.LandingKey` (MovesC/Defs),
`Moves.IsDevelopment` (Moves/Defs), `MovesT.IrrHalts`/`accE`/`accF`
(MovesT/Defs).  Touches NO fenced MovesC/MovesT statement (new declarations
only, in `Scaffold/HDischarge/H6/`).
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU1
import LeanUrat.Scaffold.HDischarge.H6.Emission
import LeanUrat.Scaffold.HDischarge.H6.EngineConform

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The terminal side-read vocabulary (the "SideReads-style" clauses at the
terminal index — C0's observable spec) -/

/-- C0 vocabulary — the terminal-frame COEFFICIENT WEIGHT, read off the last
machine node: `w_{k′+1}(B) = e_last · w_{k′}(B)` on `C_{Φterm}` coefficients.
Provenance: the child-stage stretch law `Stage.hStretch` (DEF-4,
`w B = e·wPrev B`), whose scale factor at the terminal frame is the last
READ's `e` (the frame-creating read) and whose parent weight is the last
frame's recorded `σ.w`.  The only frame-(k′+1) valuation datum on machine
record. -/
def termCoeffW (m : MovesC.Node p F) (B : Polynomial ℤ_[p]) : ℤ :=
  (m.e : ℤ) * m.σ.w B

/-- C0 vocabulary — the terminal record's TOTAL SIDE WEIGHT `γ = e·u + s·h`,
recovered from its (c1)-shape fields.  This is the exact inversion of
`nodeToE`'s `u := (gam − s0·h)/e` (CU1 III-U1): (s, u) is the side's INITIAL
point in the terminal frame, so the support line of slope −h/e through it has
constant read functional `e·y + j·h = γ`. -/
def termGamma (ν : ENodeData) : ℤ :=
  (ν.e : ℤ) * (ν.u : ℤ) + (ν.s : ℤ) * (ν.h : ℤ)

/-- C0 spec vocabulary — **`SideReads`-style conformance at the terminal
index** (`lean/blueprints/HDISCHARGE_H6.md` §4 C0 spec-1's clause bundle):
the record ν's (e, h, ℓ, s, u) are genuine side data of f's development `B`
in the terminal frame, read against the frame-(k′+1) weight `termCoeffW m`
(m = the LAST machine node).  The clauses are `SideReads` (i)/(ii) transposed
to the terminal datum granularity:

* (i) SIDE — the record's line is a lower support line of the terminal point
  set `{(j, w_{k′+1}(B j))}`: `γ ≤ e·w(B j) + j·h` at every nonzero slot,
  with equality ONLY at the record's stride slots `s + e·k`, `k ≤ ℓ`;
* (ii) ENDPOINTS — both side endpoints are occupied and ON the side, and the
  initial height IS the recorded `u`: `B s ≠ 0` with `w_{k′+1}(B s) = u`,
  and `B (s + e·ℓ) ≠ 0` on the line.

No `pat`/anchor/successor-key/vertex clause: those `SideReads` conjuncts
((ii)-digits, (iii)–(vi)) live at the machine `Node` payload, OUTSIDE the
terminal record's (e, h, ℓ, s, u, sel = ⊥) datum granularity (the §9.2a
caveat, displayed at A5). -/
def TerminalSideReads (m : MovesC.Node p F) (ν : ENodeData)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) : Prop :=
  -- (i) SIDE: support …
  ((∀ j : ℕ, j < Nd → B j ≠ 0 →
      termGamma ν ≤ (ν.e : ℤ) * termCoeffW m (B j) + (j : ℤ) * (ν.h : ℤ)) ∧
   -- … with equality only at the recorded stride slots
   (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * termCoeffW m (B j) + (j : ℤ) * (ν.h : ℤ) = termGamma ν →
      ∃ k : ℕ, k ≤ ν.ℓ ∧ j = ν.s + ν.e * k)) ∧
  -- (ii) ENDPOINTS: initial point occupied at the recorded height u …
  (B ν.s ≠ 0 ∧ termCoeffW m (B ν.s) = (ν.u : ℤ)) ∧
  -- … and the far endpoint occupied, on the side
  (B (ν.s + ν.e * ν.ℓ) ≠ 0 ∧
    (ν.e : ℤ) * termCoeffW m (B (ν.s + ν.e * ν.ℓ))
        + ((ν.s + ν.e * ν.ℓ : ℕ) : ℤ) * (ν.h : ℤ) = termGamma ν)

/-- C0 spec vocabulary — **the terminal read** of (f, M): ν is a sel-none
record whose shape fields are read from f's development in the terminal frame
(frame `M.nodes.length`).  The terminal key is the last read's landing key
(the `ReadsOf`-designated final key's own clause, `MovesC.LandingKey`); the
development is the corpus `IsDevelopment`; the read is either the finite-side
conformance `TerminalSideReads`, or the slope-−∞ branch `B 0 = 0` (the key
divides f — the j₀ = 1 sub-case of CUC §9.2, carried on exactly the clause
A6b's certificate demands of a −∞ side; shape fields NOT pinned there — the
§9.2a granularity caveat, displayed in the file header).

NON-CIRCULARITY (the C0 pin's point): every clause reads f, the machine
record M, and the development — NO GMNData, no semantic side list, no true
factor. -/
def TerminalRead (f : Polynomial ℤ_[p]) (M : MovesC.History p F)
    (ν : ENodeData) : Prop :=
  ν.sel = none ∧
  ∃ (Φterm : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
    MovesC.LandingKey (M.nodes.getLast M.nonempty) Φterm ∧
    LeanUrat.Moves.IsDevelopment Φterm f B Nd ∧
    (TerminalSideReads (M.nodes.getLast M.nonempty) ν B Nd ∨ B 0 = 0)

/-- C0 residue row (NAMED, displayed — the group's honest-residue rule):
a conformant terminal record EXISTS for (f, M).  At a genuine DEC(τ-irr)
seam this is Lemma CU-2t 9.1(i) content (the unique length-1 side of
N_{k′+1}⁻(f); consumes the perimeter disc f ≠ 0 + the seam hypotheses — NOT
derivable from `ReadsOf` alone, so spec-1 below is faithfully CONDITIONAL on
this row).  Discharge owed at C1 (k′ = 0, the PROVE door) and the
OL-conditional k′ ≥ 1 leg (blueprint §3.3); assumed NOWHERE in this file. -/
abbrev TerminalReadExists (f : Polynomial ℤ_[p])
    (M : MovesC.History p F) : Prop :=
  ∃ ν : ENodeData, TerminalRead f M ν

/-! ## The C0 def — `terminalReadRecord` (pinned signature; implementation
free = choice-on-spec, the ratified `polOM` pattern) -/

/-- The junk sel-none record (the off-spec default; every `ENodeData` law row
holds at (1, 1, 1, 0, 0, none, false)). -/
def terminalJunk : ENodeData where
  e := 1
  h := 1
  ℓ := 1
  s := 0
  u := 0
  sel := none
  inc := false
  he := le_refl 1
  hh := le_refl 1
  hcop := Nat.gcd_self 1
  hl := le_refl 1
  hsel := by intro gμ hgμ; simp at hgμ

open Classical in
/-- **H6-C0 (TRM), the terminal-read materialization** — signature = the
PINNED observable I/O of `lean/blueprints/HDISCHARGE_H6.md` §4 unit C0:
inputs (M, hM, hR, f) with NO GMNData; output a sel-none `ENodeData`.  Body
(free): the classically chosen `TerminalRead`-conformant record when one
exists, else `terminalJunk`.  The record is thereby READ FROM f's development
in the terminal frame — the spec `TerminalRead` mentions no semantic datum.
(`hM`/`hR` are the pin's certificate inputs; this choice-on-spec body does
not consume them — consumers hold them at the pinned signature, and the
C1/C2 discharge legs do.) -/
noncomputable def terminalReadRecord (n : ℕ) (f : Polynomial ℤ_[p])
    (M : MovesC.History p F) (_hM : MovesC.HistoryCoherent M)
    (_hR : LeanUrat.MovesJ.ReadsOf p F n f M) : ENodeData :=
  if h : TerminalReadExists f M then Exists.choose h else terminalJunk

/-! ## spec-1 — the conformance theorems -/

/-- C0 spec-1a (unconditional): the materialized record is TERMINAL —
`sel = none` on both branches. -/
theorem terminalReadRecord_sel_none (n : ℕ) (f : Polynomial ℤ_[p])
    (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M)
    (hR : LeanUrat.MovesJ.ReadsOf p F n f M) :
    (terminalReadRecord n f M hM hR).sel = none := by
  unfold terminalReadRecord
  by_cases h : TerminalReadExists f M
  · rw [dif_pos h]
    exact (Exists.choose_spec h).1
  · rw [dif_neg h]
    rfl

/-- **C0 spec-1** — `SideReads`-style conformance of the materialized
record's (e, h, ℓ, s, u) to f's development in the terminal frame,
CONDITIONAL on the named existence row `TerminalReadExists f M` (the honest
form — see the row's docstring: the unconditional statement is FALSE at junk
(f, M), and the existence at genuine seams is C1's/OL's owed mathematics,
not this unit's to assume). -/
theorem terminalReadRecord_conforms (n : ℕ) (f : Polynomial ℤ_[p])
    (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M)
    (hR : LeanUrat.MovesJ.ReadsOf p F n f M)
    (h : TerminalReadExists f M) :
    TerminalRead f M (terminalReadRecord n f M hM hR) := by
  unfold terminalReadRecord
  rw [dif_pos h]
  exact Exists.choose_spec h

/-! ## spec-2 — the emission tie: `engineEmission`, the C0 upgrade of B1's SV
body (ν := the TRM record) -/

/-- **H6-C0 spec-2 carrier — the canonical emission, TRM-pinned** (the B1
honesty display's promised upgrade: "the C0 upgrade `engineEmission` (ν :=
the TRM record) is where tREAD becomes provable").  `reaches` and `emitsHen`
are VERBATIM B1's SV bodies; `emits` is the SV body PLUS the pin
`ν = terminalReadRecord n f M hM hR` at the realizing run — the emitted
record is no longer free junk but THE terminal read of the witnessing
machine history.  (The certificate binders (hM, hR) move into the ∃ so the
pin can consume them at the pinned signature.) -/
noncomputable def engineEmission (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : TerminalEmission p F where
  reaches f H := ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧ (machineEHist M).continuingPart = H
  emits f H ν EF := ν.sel = none ∧ DecIrrSeam H ∧
      (∀ ν' ∈ H.nodes, ν'.sel ≠ none) ∧
      ∃ (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M)
        (hR : LeanUrat.MovesJ.ReadsOf p F n f M),
        (machineEHist M).continuingPart = H ∧
        MovesT.IrrHalts M ∧ EF = (MovesT.accE M, MovesT.accF M) ∧
        ν = terminalReadRecord n f M hM hR
  emitsHen f H EF := H.nodes = [] ∧ EF = (1, H.psi0.natDegree) ∧
      ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        (machineEHist M).continuingPart = H
  emits_terminal := fun _ _ _ _ h => h.1
  emits_reaches := fun _ _ _ _ h => by
    obtain ⟨-, -, -, M, hM, hR, hpart, -, -, -⟩ := h
    exact ⟨M, hM, hR, hpart⟩
  emitsHen_reaches := fun _ _ _ h => h.2.2
  reaches_continuing := fun _ H h ν hν => by
    obtain ⟨M, -, -, rfl⟩ := h
    have hmem : ν ∈ (machineEHist M).nodes.takeWhile
        (fun ν' => ν'.sel.isSome) := hν
    have hsome := List.mem_takeWhile_imp
      (p := fun ν' : ENodeData => ν'.sel.isSome) hmem
    exact Option.isSome_iff_ne_none.mp hsome

/-- C0 spec-2, "exactly" — the emission tie as an iff: `engineEmission`'s
emits IS B1's SV admission AND the ν-pin to the TRM record of a realizing
run (`lean/blueprints/HDISCHARGE_H6.md` §4 C0: "emits holds exactly at
(ν = terminalReadRecord …) — upgrading B1's SV body"). -/
theorem engineEmission_emits_iff (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ) :
    (engineEmission n p F).emits f H ν EF ↔
      ((engineEmissionSV n p F).emits f H ν EF ∧
        ∃ (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M)
          (hR : LeanUrat.MovesJ.ReadsOf p F n f M),
          (machineEHist M).continuingPart = H ∧
          MovesT.IrrHalts M ∧ EF = (MovesT.accE M, MovesT.accF M) ∧
          ν = terminalReadRecord n f M hM hR) := by
  constructor
  · rintro ⟨hsel, hdec, hcont, M, hM, hR, hpart, hirr, hEF, hpin⟩
    exact ⟨⟨hsel, hdec, hcont, M, hM, hR, hpart, hirr, hEF⟩,
      M, hM, hR, hpart, hirr, hEF, hpin⟩
  · rintro ⟨⟨hsel, hdec, hcont, -⟩, M, hM, hR, hpart, hirr, hEF, hpin⟩
    exact ⟨hsel, hdec, hcont, M, hM, hR, hpart, hirr, hEF, hpin⟩

/-- C0 spec-2, the upgrade direction displayed: every TRM-pinned emission is
an SV admission (the pin only RESTRICTS B1's body — no consumer weakens). -/
theorem engineEmission_emits_SV (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ)
    (h : (engineEmission n p F).emits f H ν EF) :
    (engineEmissionSV n p F).emits f H ν EF :=
  ((engineEmission_emits_iff n f H ν EF).mp h).1

/-- C0 spec-2 rider: the upgraded emission's `reaches` is DEFINITIONALLY B1's
(so `EngineCovers`-type facts transfer verbatim to the D1a packaging). -/
theorem engineEmission_reaches_iff_SV (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) :
    (engineEmission n p F).reaches f H ↔
      (engineEmissionSV n p F).reaches f H :=
  Iff.rfl

/-- **C0 spec-2 rider — the `EngineTied` re-proof** at the upgraded emission
(the blueprint's "`EngineTied` re-proof rides along"): `reaches` is literally
the realization clause; `emits` projects to it (the pin adds only the ν
constraint, which `EngineTied` does not read — shape-tying stays owed at the
C1/C2 legs, per B0's deliberate scope). -/
theorem engineEmission_engineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    EngineTied n p F (engineEmission n p F) where
  reaches_engine := fun _ _ h => h
  emits_irr_verdict := fun _ _ _ _ h _ => by
    obtain ⟨-, -, -, M, hM, hR, hpart, hirr, hEF, -⟩ := h
    exact ⟨M, hM, hR, hpart, hirr, hEF⟩

end LeanUrat.Scaffold.HDischarge.H6
