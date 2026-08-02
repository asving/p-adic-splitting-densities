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
import LeanUrat.Scaffold.DictIII.GDOrder1
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

/-! ## Unit C2 — (T-READ) k′ ≥ 1: the terminal binding at the engine + the
OL-2-min instance routing (`lean/blueprints/HDISCHARGE_H6.md` §4 unit C2;
§3.3(b)/(c))

DESIGN RECORD (C2 is prose-specced — blueprint §4 C2 displays NO Lean block,
the C0 precedent; the statements below transcribe its clauses at the C0
vocabulary; every interpretive choice displayed):

* **The binding (§3.3(b), GD-4 bookkeeping)** — "the emitted terminal record
  IS the record of the level-(k′+1) stage read": DEFINITIONAL once C0 lands,
  because `engineEmission`'s emits body PINS ν = `terminalReadRecord` of a
  realizing certified run.  `engineEmission_terminal_binding` extracts exactly
  that clause — the terminal analogue of OL-6's per-read `SideReads` binding.
* **The named hypothesis (§3.3(c))** — `OL2minTerminal`: the OL-2-min
  INSTANCE at the requested (terminal) level k′+1.  The landed
  `DictIII/Hyps.OL2min` stops strictly BELOW the terminal index (its range is
  `i < c.slopes.length`, and `(Theta H).slopes.length = H.nodes.length` on
  continuing seams), so the instance is a NEW named row: clause (i) = the
  OL-2-min nonemptiness clause verbatim AT index `H.nodes.length`; clause
  (ii) = the GD-2 read-semantics face keyed at C0's `TerminalRead`
  vocabulary — at every certified realizing run the conformant terminal
  record EXISTS (C0's `TerminalReadExists` residue, whose k′ ≥ 1 leg C0's
  header routes exactly here) and every conformant record's (e, h, ℓ, s, u)
  is every listed side's datum.  NAMED HYPOTHESIS ROW consumed as an
  antecedent — never an axiom, never discharged by fiat.
* **Order ≥ 2 routing = the (H1) consumption, NO proof attempted** — the one
  displayed router lemma `ol2minTerminal_of_properness`: at terminal index
  k′ ≥ 2, clause (i) is EXACTLY `GRB.properness` (III-H1, the (H1) group's
  landed row, guard `2 ≤ i` — the "≥ 2 content routes through GRB" arrow of
  `DictIII/Hyps.lean`, fired at the requested level); clause (ii) rides as
  the NAMED residual antecedent.  Pure plumbing: the order-≥ 2 mathematics
  lives in the (H1) rows, priced once, there.
* **Order ≤ 1 (the k′ = 1 terminal index, the order-1 dictionary) — the
  honest HEAD state, displayed**: the piece the LANDED `DictIII/GDOrder1.lean`
  discharges is the development-identity layer (the same read-conformance
  content CU-1's step consumed) — the terminal key's φ-adic development of f
  EXISTS, `terminalKey_development_exists` below from
  `isDevelopment_devCoeff` (slot-uniqueness is the landed converse
  `devCoeff_eq_of_isDevelopment`).  The POLYGON face of the k′ = 1 instance
  is NOT dischargeable at HEAD: GDOrder1's order-1 weight layer (`w1`/
  `gaussW`, units III-G3a/G4) is BLOCKED (typeclass-stuck defs, recorded
  there), and the canonical order-≤ 1 constructor `gmnDataOrder1` is
  deep-truncated (`principalSides (i+1) = []`), so clause (i) is FALSE at the
  canonical datum at any k′ ≥ 1 — the k′ = 1 instance stays with the row
  (this group's priced residue), consumed hypothetically only.  NOT papered
  over; no sorry rides this unit.
* **MOP-UP RE-CHECK (2026-08-02, HEAD `baa5332`)**: the upstream block
  re-checked — `DictIII/GDOrder1.lean` units III-G3a/G4/G6 (`gaussW`/`w1`)
  remain BLOCKED (typeclass-stuck, per their standing records), and
  `gmnDataOrder1` remains deep-truncated; the k′ = 1 polygon-face residue
  therefore STANDS unchanged, with the row. -/

/-- **H6-C2a — the terminal-binding clause at the engine** (blueprint §3.3(b),
definitional once C0 lands): every record emitted by `engineEmission` IS the
TRM record (`terminalReadRecord`) of a realizing certified machine run — the
exact clause OL-6 supplies for continuing records and exempts for terminal
ones, supplied at the terminal record by C0's pin.  Pure projection of the
emits body. -/
theorem engineEmission_terminal_binding (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ)
    (h : (engineEmission n p F).emits f H ν EF) :
    ∃ (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M)
      (hR : LeanUrat.MovesJ.ReadsOf p F n f M),
      (machineEHist M).continuingPart = H ∧
      ν = terminalReadRecord n f M hM hR := by
  obtain ⟨-, -, -, M, hM, hR, hpart, -, -, hpin⟩ := h
  exact ⟨M, hM, hR, hpart, hpin⟩

/-- **H6-C2b — THE NAMED HYPOTHESIS ROW: the OL-2-min instance at the
requested (terminal) level k′+1** (blueprint §3.3(c); CUC §9.4 pricing:
"already-priced GD-2-family residue").  Clause (i): the OL-2-min nonemptiness
clause (`DictIII/Hyps.OL2min`'s body) at the terminal index `H.nodes.length`
— one past `OL2min`'s own range, which is why the instance is a NEW row.
Clause (ii): the GD-2 read-semantics face at C0's `TerminalRead` vocabulary —
at every certified realizing run the conformant terminal record exists, and
every conformant record's (e, h, ℓ, s, u) is every listed side's datum (the
development-read ↔ `D.principalSides` bridge the C0 header names as C1/C2's
content).  [M]-grade: consumed as an antecedent below, discharged nowhere in
this file; order-≤ 1/≥ 2 routing per the section header. -/
def OL2minTerminal (n : ℕ) (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  D.principalSides H.nodes.length ≠ [] ∧
  ∀ (M : MovesC.History p F),
    MovesC.HistoryCoherent M →
    LeanUrat.MovesJ.ReadsOf p F n f M →
    (machineEHist M).continuingPart = H →
    TerminalReadExists f M ∧
    ∀ ν : ENodeData, TerminalRead f M ν →
      ∀ S ∈ D.principalSides H.nodes.length,
        (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u)

/-- **H6-C2c — `tREAD`'s k′ ≥ 1 face at the engine, proved from the named row
+ the binding** (blueprint §4 C2's demanded theorem).  Antecedents = A7's
`tREAD` row antecedents VERBATIM (`ReadThroughIota` + `ConsF` standing, the
emission, the decided seam) + the face guard `H.nodes ≠ []` + the named row
`OL2minTerminal`; conclusion = `tREAD`'s NONEMPTY + ∀-SIDES conclusion
VERBATIM.  Proof: the binding pins ν to the realizing run's TRM record; the
row supplies existence (so C0's spec-1 fires) and the sides' datum. -/
theorem tREAD_kge1_of_OL2minTerminal (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D)
    (_hread : ReadThroughIota f H D) (_hcons : ConsF f H D R)
    (hOL : OL2minTerminal n f H D)
    (hem : (engineEmission n p F).emits f H ν EF)
    (_hdec : DecSeam f H D) (_hk : H.nodes ≠ []) :
    D.principalSides H.nodes.length ≠ [] ∧
    ∀ S ∈ D.principalSides H.nodes.length,
      (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u) := by
  obtain ⟨M, hM, hR, hpart, hpin⟩ :=
    engineEmission_terminal_binding n f H ν EF hem
  obtain ⟨hex, hconf⟩ := hOL.2 M hM hR hpart
  refine ⟨hOL.1, fun S hS => ?_⟩
  rw [hpin]
  exact hconf _ (terminalReadRecord_conforms n f M hM hR hex) S hS

/-- **H6-C2d — the (H1)-consumption ROUTER (the one displayed router lemma;
NO order-≥ 2 proof attempted)**: at terminal index k′ ≥ 2 the row's OL-2-min
nonemptiness clause (i) is EXACTLY the (H1) group's landed `GRB.properness`
(III-H1, guard `2 ≤ i`), and the read-semantics clause (ii) stays the NAMED
residual antecedent `hsem` — the (H1)-riding half, its mathematics priced
ONCE, at (H1); nothing here proves, weakens, or discharges it. -/
theorem ol2minTerminal_of_properness (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (D : GMNData f (Theta H))
    (hGRB : GRB p F) (hk : 2 ≤ H.nodes.length)
    (hsem : ∀ (M : MovesC.History p F),
      MovesC.HistoryCoherent M →
      LeanUrat.MovesJ.ReadsOf p F n f M →
      (machineEHist M).continuingPart = H →
      TerminalReadExists f M ∧
      ∀ ν : ENodeData, TerminalRead f M ν →
        ∀ S ∈ D.principalSides H.nodes.length,
          (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u)) :
    OL2minTerminal n f H D :=
  ⟨hGRB.properness H.nodes.length hk, hsem⟩

/-- **H6-C2e — the GDOrder1 (order ≤ 1) discharge, the landed piece**: the
development-identity layer of the instance — the terminal key's φ-adic
development of f exists, supplied by the landed order-≤ 1 dictionary
(`isDevelopment_devCoeff`, unit III-G1; slot-uniqueness is its landed
converse `devCoeff_eq_of_isDevelopment`).  This is the layer C0's
`TerminalRead` quantifies over (`∃ B Nd, IsDevelopment Φterm f B Nd`).  The
POLYGON face of the k′ = 1 instance is NOT dischargeable at HEAD — see the
section header's honest-state display (GDOrder1 `w1`/`gaussW` BLOCKED;
`gmnDataOrder1` deep-truncated). -/
theorem terminalKey_development_exists (f Φterm : Polynomial ℤ_[p])
    (hmonic : Φterm.Monic) (hdeg : 1 ≤ Φterm.natDegree) :
    ∃ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ),
      LeanUrat.Moves.IsDevelopment Φterm f B N :=
  ⟨devCoeff Φterm f, f.natDegree + 1, isDevelopment_devCoeff hmonic hdeg f⟩

/-! ## Unit C1 — (T-READ) k′ = 0 conformance at order ≤ 1
(`lean/blueprints/HDISCHARGE_H6.md` §4 unit C1; §3.3(a), the PROVE door)

STATEMENT PROVENANCE (C1 is prose-specced — blueprint §4 C1 displays NO Lean
block, the C0/C2 precedent in this file): the unit statement is A7's `tREAD`
row (displayed VERBATIM at blueprint §4 A7 and landed VERBATIM in
`H6/Emission.lean` `TerminalSeamHypsE.tREAD`) specialized per the C1 prose,
token-for-token in antecedents and conclusion:
* `E := engineEmission n p F` ("tREAD for `engineEmission`");
* the `DecSeam` hypothesis restricted to `DecHenSeam` ("restricted to
  `DecHenSeam` seams");
* `D := gmnDataOrder1 f (Theta H) ιb ι0 hlen` ("against the order-≤ 1
  `GMNData` constructor").
No other token differs from the A7 row.  That specialized row is
`tREAD_engineEmission_decHen_order1` below.

HONESTY DISPLAY — how the row discharges, and where the mathematics lives:

* **The row itself discharges STRUCTURALLY (channel discipline), and this is
  displayed, not hidden**: `engineEmission`'s record channel `emits` carries
  the `DecIrrSeam` conjunct (`H.nodes ≠ []`, B1's SV body upgraded at C0),
  while `DecHenSeam` demands `H.nodes = []` — at the AS-BUILT engine no
  ENodeData record is ever emitted at a hen seam (the machine reality the
  fold-round-1 Codex-finding-1 repair encoded: hen bookings ride the
  verdict-pair-only `emitsHen` channel; "at a₀ = 1 the seam object is (ρ₀) +
  machine record with NO terminal ENodeData", CUC §9.1 carrier note, and W3's
  a₀ ≥ 2 terminal-node permission is likewise not an `emits` admission).
  `engineEmission_emits_not_decHenSeam` displays the exact contradiction; the
  pinned row follows.  This is the same engine-level discharge pattern the
  blueprint itself prices for `tDECcor`'s corner fence (§3.2: "discharging
  the fence VACUOUSLY at the engine").
* **The §3.3(a) mathematics — the (c1)-shape read content — is therefore owed
  NON-VACUOUSLY, and lands below at the corpus base-polygon layer** (the
  PROVE door's own address: "PROVE, at the corpus base-polygon layer"):
  `principalData_hensel_a0_one` proves that at the Hensel-simple
  configuration (a₀ = 1 ∧ j₀ = 0, read at the X-key: constant slot of
  positive valuation, degree-1 slot a unit) the corpus principal polygon
  `N₁⁻(f)` has EXACTLY ONE side, of length 1 — CUC §9.3(i) "total length 1
  and exactly one side" — with the (c1) datum (e, h, ℓ, s, u)
  = (1, v(c₀), 1, 0, v(c₀)); `tREAD_conclusion_hensel_k0` /
  `tREAD_shape_hensel_k0` restate this as `tREAD`'s NONEMPTY + ∀-SIDES
  conclusion VERBATIM at the order-≤ 1 constructor and terminal index k′ = 0.
  The j₀ = 1 branch (`negInfty_read_witness_k0`) carries the slope-−∞ side on
  EXACTLY the clause A6b's certificate demands of a −∞ side (`B 0 = 0`, the
  key divides f), on the X-key development supplied by the landed order-≤ 1
  dictionary; `decHenSeam_gmnDataOrder1_iff` compiles the III-A6a scope fact
  that the corpus constructor LISTS no −∞ side (the GMN Def 1.1 −∞ side has
  no `npSides` representative), so at the order-≤ 1 datum the hen seam's
  −∞ disjunct routes entirely through the a₀ = 1 channel; and
  `decHenSeam_rootOrd_pin` pins the booking to `rootOrder0 = 1` (the
  Hensel-simple residual factor) under `ConsF`.

DISPLAYED RESIDUE (nothing silently resolved):
* the ψ̂₀-KEY ALIGNMENT SEAM: the corpus base read is the COEFFICIENT polygon
  (abscissae are X-powers — the III-A6a scope caveat, quoted at A6b), so the
  Hensel-branch hypotheses below are the a₀ = 1 ∧ j₀ = 0 configuration READ
  AT THE X-KEY (`f.coeff 0/1` slots); the tie from `H.a0 = 1` at a general
  dressed key ψ̂₀ to these coefficient hypotheses is the same III-A6a caveat
  every order-≤ 1 consumer carries — displayed here, discharged nowhere.
* the machine-side existence tie (C0's `TerminalReadExists` at a realized
  k′ = 0 run — `TerminalSideReads` against the machine frame weight
  `termCoeffW`) remains C0's named residue row, assumed nowhere in this file;
  this unit discharges the D-side (polygon) read content the C0 header
  routes to C1. -/

section UnitC1

open LeanUrat.OM

/-- **H6-C1a — the channel-discipline fact, displayed**: at the as-built
engine the record channel is empty on hen seams — `engineEmission`'s `emits`
admits only `DecIrrSeam` (`H.nodes ≠ []`) seams, and a `DecHenSeam` seam has
`H.nodes = []`.  The k′ = 0 face of `tREAD` at the engine discharges through
exactly this fact (see the section header's honesty display). -/
theorem engineEmission_emits_not_decHenSeam (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ)
    (D : GMNData f (Theta H))
    (hem : (engineEmission n p F).emits f H ν EF)
    (hdec : DecHenSeam f H D) : False :=
  hem.2.1.1 hdec.1

/-- **H6-C1 (THE unit row) — (T-READ) k′ = 0 at order ≤ 1**: A7's `tREAD` row
VERBATIM, specialized per the blueprint §4 C1 prose — `E := engineEmission`,
`DecSeam` restricted to `DecHenSeam`, `D :=` the order-≤ 1 constructor
`gmnDataOrder1`.  Discharge: structural, by the displayed channel discipline
(`engineEmission_emits_not_decHenSeam`); the non-vacuous (c1)-read content of
§3.3(a) lands in `principalData_hensel_a0_one` /
`tREAD_conclusion_hensel_k0` / `negInfty_read_witness_k0` below — see the
section header before consuming this row as "(T-READ) k′ = 0 discharged". -/
theorem tREAD_engineEmission_decHen_order1 (n : ℕ) (f : Polynomial ℤ_[p])
    (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ)
    (ιb : ZMod p →+* ↥(Theta H).base) (ι0 : ZMod p →+* ↥((Theta H).fld 0))
    (hlen : (Theta H).slopes.length ≤ 1)
    (R : GMNReader f (Theta H) (gmnDataOrder1 f (Theta H) ιb ι0 hlen))
    (_hread : ReadThroughIota f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen))
    (_hcons : ConsF f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen) R)
    (hem : (engineEmission n p F).emits f H ν EF)
    (hdec : DecHenSeam f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen)) :
    (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides H.nodes.length ≠ [] ∧
    ∀ S ∈ (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides H.nodes.length,
      (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u) :=
  absurd hdec.1 hem.2.1.1

/-! ### The seam-routing lemmas at the order-≤ 1 constructor -/

/-- Every datum the corpus constructor lists is finite-slope — the III-A6a
scope fact compiled (`sideToDatum` stamps `isNegInfty := false`; the GMN
Def 1.1 slope-−∞ side has no `npSides` representative). -/
theorem principalData_isNegInfty_false (f : Polynomial ℤ_[p]) :
    ∀ T ∈ principalData f, T.isNegInfty = false := by
  intro T hT
  obtain ⟨S, -, -, rfl⟩ := mem_principalData hT
  rfl

/-- **H6-C1 routing** — at the order-≤ 1 constructor the hen seam's −∞
disjunct is unrepresentable (no listed −∞ side), so `DecHenSeam` routes
entirely through the a₀ = 1 channel: `DecHenSeam f H (gmnDataOrder1 …) ↔
H.nodes = [] ∧ H.a0 = 1`.  The REAL j₀ = 1 content is carried instead on the
development clause `B 0 = 0` (`negInfty_read_witness_k0`), the exact −∞
vocabulary A6b's certificate uses. -/
theorem decHenSeam_gmnDataOrder1_iff (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ιb : ZMod p →+* ↥(Theta H).base) (ι0 : ZMod p →+* ↥((Theta H).fld 0))
    (hlen : (Theta H).slopes.length ≤ 1) :
    DecHenSeam f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen) ↔
      H.nodes = [] ∧ H.a0 = 1 := by
  have hps : (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides 0
      = principalData f := by
    simp [gmnDataOrder1]
  constructor
  · rintro ⟨hn, ha | ⟨T, hT, hneg⟩⟩
    · exact ⟨hn, ha⟩
    · rw [hps] at hT
      rw [principalData_isNegInfty_false f T hT] at hneg
      exact absurd hneg (by simp)
  · rintro ⟨hn, ha⟩
    exact ⟨hn, Or.inl ha⟩

/-- **H6-C1 booking pin** — under `ConsF` a hen-decided seam at the order-≤ 1
constructor pins the genuine root order to 1: `rootOrder0 f (Theta H) ιb = 1`
(the Hensel-simple residual factor — ord_{ψ̂₀}(f̄) = 1, read through ιb). -/
theorem decHenSeam_rootOrd_pin (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ιb : ZMod p →+* ↥(Theta H).base) (ι0 : ZMod p →+* ↥((Theta H).fld 0))
    (hlen : (Theta H).slopes.length ≤ 1)
    (R : GMNReader f (Theta H) (gmnDataOrder1 f (Theta H) ιb ι0 hlen))
    (hcons : ConsF f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen) R)
    (hdec : DecHenSeam f H (gmnDataOrder1 f (Theta H) ιb ι0 hlen)) :
    rootOrder0 f (Theta H) ιb = 1 := by
  have ha0 : H.a0 = 1 :=
    ((decHenSeam_gmnDataOrder1_iff f H ιb ι0 hlen).mp hdec).2
  have h1 : R.rootOrd = H.a0 := hcons.1
  have h2 : R.rootOrd = (gmnDataOrder1 f (Theta H) ιb ι0 hlen).rootOrder :=
    R.rootOrd_spec
  have h3 : (gmnDataOrder1 f (Theta H) ιb ι0 hlen).rootOrder
      = rootOrder0 f (Theta H) ιb := rfl
  rw [← h3, ← h2, h1, ha0]

/-! ### The j₀ = 1 branch — the slope-−∞ side as a development read -/

/-- **H6-C1, j₀ = 1 branch (the slope-−∞ side, CUC §9.2 convention)**: when
the key divides f (`f.coeff 0 = 0` at the X-key — j₀ ≥ 1), the level-1
development of f w.r.t. the key has a VANISHING 0-slot — `B 0 = 0`, EXACTLY
the clause A6b's certificate demands of a listed −∞ side and EXACTLY C0's
`TerminalRead` −∞ branch.  The development is the landed order-≤ 1
dictionary's (`devCoeff`, unit III-G1); the −∞ branch pins NO shape fields
(the §9.2a datum-granularity caveat, displayed at C0). -/
theorem negInfty_read_witness_k0 (f : Polynomial ℤ_[p])
    (hc0 : f.coeff 0 = 0) :
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      LeanUrat.Moves.IsDevelopment (Polynomial.X : Polynomial ℤ_[p]) f B Nd ∧
      B 0 = 0 := by
  refine ⟨devCoeff Polynomial.X f, f.natDegree + 1,
    isDevelopment_devCoeff Polynomial.monic_X (by simp) f, ?_⟩
  show f %ₘ Polynomial.X = 0
  rw [Polynomial.modByMonic_X, ← Polynomial.coeff_zero_eq_eval_zero, hc0,
    Polynomial.C_0]

/-! ### The a₀ = 1 ∧ j₀ = 0 branch — THE core: the unique finite side of
`N₁⁻(f)`, at the corpus base-polygon layer (CUC §9.3(i); CU-2t 9.1(i)) -/

/-- List helper: a strictly-sorted `ℕ`-list containing 0 and 1 starts
`0 :: 1 ::` and its tail sits at abscissae ≥ 2. -/
private lemma c1_sorted_zero_one {l : List ℕ}
    (hsort : l.Pairwise (· < ·)) (h0 : 0 ∈ l) (h1 : 1 ∈ l) :
    ∃ t, l = 0 :: 1 :: t ∧ ∀ j ∈ t, 2 ≤ j := by
  cases l with
  | nil => simp at h0
  | cons a t =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsort
    have ha : a = 0 := by
      rcases List.mem_cons.mp h0 with heq | hmem
      · omega
      · have := hhead 0 hmem; omega
    subst ha
    have h1t : 1 ∈ t := by
      rcases List.mem_cons.mp h1 with heq | hmem
      · exact absurd heq (by omega)
      · exact hmem
    cases t with
    | nil => simp at h1t
    | cons b t' =>
      obtain ⟨hhead', htail'⟩ := List.pairwise_cons.mp htail
      have hb : b = 1 := by
        rcases List.mem_cons.mp h1t with heq | hmem
        · omega
        · have h1b := hhead' 1 hmem
          have hb0 := hhead b (by simp)
          omega
      subst hb
      exact ⟨t', rfl, fun j hj => by have := hhead' j hj; omega⟩

/-- List helper: consecutive pairs of an abscissa-sorted dot list have
strictly increasing abscissae. -/
private lemma c1_zip_tail_fst_lt {l : List (ℕ × ℕ)}
    (hsort : (l.map Prod.fst).Pairwise (· < ·)) :
    ∀ pr ∈ l.zip l.tail, pr.1.1 < pr.2.1 := by
  induction l with
  | nil => intro pr hpr; simp at hpr
  | cons a t ih =>
    intro pr hpr
    cases t with
    | nil => simp at hpr
    | cons b t' =>
      rw [List.map_cons] at hsort
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsort
      simp only [List.tail_cons, List.zip_cons_cons] at hpr
      rcases List.mem_cons.mp hpr with heq | hpr'
      · subst heq
        exact hhead b.1 (by simp)
      · exact ih htail pr hpr'

/-- Hull helper: `dropCollinear` keeps the first two entries whenever the
head pair is non-collinear with every deeper dot. -/
private lemma c1_dropCollinear_two_head (a b : ℕ × ℕ) (t : List (ℕ × ℕ))
    (hnc : ∀ P ∈ t, NewtonPolygon.collinear₃ a b P = false) :
    ∃ w, NewtonPolygon.dropCollinear (a :: b :: t) = a :: b :: w := by
  cases t with
  | nil => exact ⟨[], rfl⟩
  | cons c restM =>
    obtain ⟨u, hu, husub⟩ := NewtonPolygon.dropCollinear_cons_head b (c :: restM)
    rw [NewtonPolygon.dropCollinear_cons3, hu]
    cases u with
    | nil => exact ⟨[], rfl⟩
    | cons c' u' =>
      refine ⟨c' :: u', ?_⟩
      have hcol : NewtonPolygon.collinear₃ a b c' = false :=
        hnc c' (husub.subset (by simp))
      show (if NewtonPolygon.collinear₃ a b c' = true then a :: c' :: u'
        else a :: b :: c' :: u') = a :: b :: c' :: u'
      rw [hcol]
      simp

/-- The (c1) datum of the Hensel side: slope −v₀/1, so `e = 1`,
`h = |−v₀| = v₀`, degree `ℓ = 1`, initial point `(s, u) = (0, v₀)`. -/
private lemma c1_side_datum (v₀ : ℕ) :
    (⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side).e = 1 ∧
    (⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side).h = -(v₀ : ℤ) ∧
    M4.residualDeg (⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side) = 1 := by
  have hsl : (⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side).slope = ((-(v₀ : ℤ) : ℤ) : ℚ) := by
    simp only [NewtonPolygon.Side.slope]
    push_cast
    norm_num
  have he1 : (⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side).e = 1 := by
    simp only [NewtonPolygon.Side.e, hsl, Rat.den_intCast]
  refine ⟨he1, ?_, ?_⟩
  · simp only [NewtonPolygon.Side.h, hsl, Rat.num_intCast]
  · simp only [M4.residualDeg, NewtonPolygon.Side.length, he1]

/-- **H6-C1 CORE, side-list form — the unique finite side at the Hensel
configuration** (§3.3(a) branch a₀ = 1 ∧ j₀ = 0; CUC §9.3(i) "total length 1
and exactly one side"; the (D3)/(L3+) simple-residual-factor face at the
X-key).  Hypotheses = the configuration read at the X-key (the III-A6a scope
caveat, displayed in the section header): the constant slot is nonzero of
positive valuation (j₀ = 0, but reducing mod p), the degree-1 slot is a unit
(a₀ = 1).  Conclusion: the corpus principal polygon has EXACTLY the one side
(0, v₀) → (1, 0), v₀ = v(f₍₀₎) — length 1.

Proof: (i) both dots are support dots and the chord through them is a valid
supporting line (all deeper dots have height ≥ 0, the chord is ≤ 0 beyond
abscissa 1), so both are ON the hull and the hull heights at 0 and 1 are v₀
and 0; (ii) the hull abscissae therefore start `0 :: 1 ::` (sortedness), and
no deeper dot is collinear with the pair (the chord drops strictly below 0),
so `npVertices` starts with exactly these two vertices; (iii) every LATER
side has slope ≥ 0 — at abscissa 1 the hull is 0, heights are ≥ 0, and
`npHeight` is CONVEX (`npHeight_convexOn` + `slope_mono_adjacent`) — so the
negative-slope filter keeps exactly the first side. -/
theorem principalSideList_hensel_a0_one (f : Polynomial ℤ_[p])
    (hc0 : f.coeff 0 ≠ 0) (hv0 : 1 ≤ (f.coeff 0).valuation)
    (hc1 : f.coeff 1 ≠ 0) (hv1 : (f.coeff 1).valuation = 0) :
    principalSideList f = [⟨0, 1, (f.coeff 0).valuation, 0⟩] := by
  set v₀ := (f.coeff 0).valuation with hv₀def
  -- the two anchor dots
  have hmem0 : ((0 : ℕ), v₀) ∈ M2.valSupport p f :=
    ((M2.valSupport_facts p f).1 0 v₀).mpr ⟨hc0, rfl⟩
  have hmem1 : ((1 : ℕ), (0 : ℕ)) ∈ M2.valSupport p f :=
    ((M2.valSupport_facts p f).1 1 0).mpr ⟨hc1, by rw [M2.coeffVal_def, hv1]⟩
  have hS : (M2.valSupport p f).Nonempty := ⟨_, hmem0⟩
  -- the chord through the anchors, and its value law
  have hslope : NewtonPolygon.pairSlope ((0 : ℕ), v₀) ((1 : ℕ), (0 : ℕ))
      = -(v₀ : ℚ) := by
    simp [NewtonPolygon.pairSlope]
  have hlineval : ∀ x : ℚ,
      NewtonPolygon.pairLine ((0 : ℕ), v₀) ((1 : ℕ), (0 : ℕ)) x
        = (v₀ : ℚ) * (1 - x) := by
    intro x
    simp only [NewtonPolygon.pairLine, hslope]
    push_cast
    ring
  have hval : (((0 : ℕ), v₀), ((1 : ℕ), (0 : ℕ)))
      ∈ NewtonPolygon.validLines (M2.valSupport p f) := by
    classical
    rw [NewtonPolygon.validLines, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨hmem0, hmem1⟩, ?_⟩
    intro Q hQ
    obtain ⟨i, v⟩ := Q
    obtain ⟨-, hvi⟩ := ((M2.valSupport_facts p f).1 i v).mp hQ
    show NewtonPolygon.pairLine _ _ ((i : ℕ) : ℚ) ≤ ((v : ℕ) : ℚ)
    rw [hlineval]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have : v = v₀ := hvi
      subst this
      norm_num
    · have h1le : (1 : ℚ) ≤ (i : ℚ) := by exact_mod_cast hi
      have hv0q : (0 : ℚ) ≤ (v₀ : ℚ) := Nat.cast_nonneg _
      have hvq : (0 : ℚ) ≤ (v : ℚ) := Nat.cast_nonneg _
      nlinarith
  -- hull heights at the anchors
  have h0 : NewtonPolygon.npHeight (M2.valSupport p f) hS 0 = (v₀ : ℚ) := by
    refine le_antisymm ?_ ?_
    · simpa using NewtonPolygon.npHeight_le (M2.valSupport p f) hS hmem0
    · have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) =>
          NewtonPolygon.pairLine PR.1 PR.2 (0 : ℚ)) hval
      refine le_trans (le_of_eq ?_) hle
      rw [hlineval]
      norm_num
  have h1 : NewtonPolygon.npHeight (M2.valSupport p f) hS 1 = 0 := by
    refine le_antisymm ?_ ?_
    · simpa using NewtonPolygon.npHeight_le (M2.valSupport p f) hS hmem1
    · have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) =>
          NewtonPolygon.pairLine PR.1 PR.2 (1 : ℚ)) hval
      refine le_trans (le_of_eq ?_) hle
      rw [hlineval]
      norm_num
  -- the hull abscissae start 0 :: 1
  have hsorted : (NewtonPolygon.hullAbscissae (M2.valSupport p f) hS).Pairwise
      (· < ·) := by
    have := NewtonPolygon.npVerticesFull_sorted (M2.valSupport p f) hS
    rwa [NewtonPolygon.npVerticesFull_fst] at this
  have habs0 : 0 ∈ NewtonPolygon.hullAbscissae (M2.valSupport p f) hS :=
    (NewtonPolygon.mem_hullAbscissae_iff _ hS).mpr
      ⟨v₀, hmem0, by push_cast; exact h0.symm⟩
  have habs1 : 1 ∈ NewtonPolygon.hullAbscissae (M2.valSupport p f) hS :=
    (NewtonPolygon.mem_hullAbscissae_iff _ hS).mpr
      ⟨0, hmem1, by push_cast; exact h1.symm⟩
  obtain ⟨rest, habs, hrest2⟩ := c1_sorted_zero_one hsorted habs0 habs1
  -- the full vertex list starts with the two anchor dots
  have hh0 : NewtonPolygon.hullHeightAt (M2.valSupport p f) hS 0 = v₀ :=
    NewtonPolygon.hullHeightAt_of_onHull _ hS hmem0 (by push_cast; exact h0.symm)
  have hh1 : NewtonPolygon.hullHeightAt (M2.valSupport p f) hS 1 = 0 :=
    NewtonPolygon.hullHeightAt_of_onHull _ hS hmem1 (by push_cast; exact h1.symm)
  have hd0 : NewtonPolygon.hullDotAt (M2.valSupport p f) hS 0 = ((0 : ℕ), v₀) := by
    simp only [NewtonPolygon.hullDotAt, hh0]
  have hd1 : NewtonPolygon.hullDotAt (M2.valSupport p f) hS 1
      = ((1 : ℕ), (0 : ℕ)) := by
    simp only [NewtonPolygon.hullDotAt, hh1]
  have hfull : NewtonPolygon.npVerticesFull (M2.valSupport p f) hS
      = ((0 : ℕ), v₀) :: ((1 : ℕ), (0 : ℕ))
        :: rest.map (NewtonPolygon.hullDotAt (M2.valSupport p f) hS) := by
    rw [NewtonPolygon.npVerticesFull, habs, List.map_cons, List.map_cons, hd0, hd1]
  -- no deeper dot is collinear with the anchor pair
  have hnc : ∀ P ∈ rest.map (NewtonPolygon.hullDotAt (M2.valSupport p f) hS),
      NewtonPolygon.collinear₃ ((0 : ℕ), v₀) ((1 : ℕ), (0 : ℕ)) P = false := by
    intro P hP
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hP
    have hj2 : 2 ≤ j := hrest2 j hj
    simp only [NewtonPolygon.hullDotAt, NewtonPolygon.collinear₃]
    rw [beq_eq_false_iff_ne]
    intro heq
    have hj2' : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj2
    have hv0' : (1 : ℤ) ≤ (v₀ : ℤ) := by exact_mod_cast hv0
    have hhh : (0 : ℤ)
        ≤ (NewtonPolygon.hullHeightAt (M2.valSupport p f) hS j : ℤ) :=
      Int.natCast_nonneg _
    push_cast at heq
    nlinarith
  -- the genuine vertex list starts with the two anchors
  have hnv : NewtonPolygon.npVertices (M2.valSupport p f) hS
      = NewtonPolygon.dropCollinear (((0 : ℕ), v₀) :: ((1 : ℕ), (0 : ℕ))
        :: rest.map (NewtonPolygon.hullDotAt (M2.valSupport p f) hS)) := by
    rw [NewtonPolygon.npVertices, hfull]
  obtain ⟨w, hw⟩ := c1_dropCollinear_two_head _ _ _ hnc
  have hveq : NewtonPolygon.npVertices (M2.valSupport p f) hS
      = ((0 : ℕ), v₀) :: ((1 : ℕ), (0 : ℕ)) :: w := hnv.trans hw
  -- the side list = the anchor side :: the deeper sides
  have hsides : NewtonPolygon.npSides (M2.valSupport p f) hS
      = (⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side)
        :: (((((1 : ℕ), (0 : ℕ)) :: w).zip w).map
          (fun pr => (⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : NewtonPolygon.Side))) := by
    rw [NewtonPolygon.npSides, hveq]
    rfl
  -- sortedness of the tail vertices
  have hvfstall := NewtonPolygon.npVertices_sorted (M2.valSupport p f) hS
  rw [hveq, List.map_cons] at hvfstall
  obtain ⟨hhead0, hsortv⟩ := List.pairwise_cons.mp hvfstall
  -- every deeper side has slope ≥ 0 (convexity through the height-0 anchor)
  have htails : ∀ pr ∈ (((1 : ℕ), (0 : ℕ)) :: w).zip w,
      0 ≤ (⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : NewtonPolygon.Side).h := by
    rintro ⟨P, R⟩ hpr
    obtain ⟨hPmem, hRmem⟩ := List.of_mem_zip hpr
    have hlt : P.1 < R.1 := c1_zip_tail_fst_lt hsortv (P, R) hpr
    have hPmem' : P ∈ NewtonPolygon.npVertices (M2.valSupport p f) hS := by
      rw [hveq]; exact List.mem_cons_of_mem _ hPmem
    have hRmem' : R ∈ NewtonPolygon.npVertices (M2.valSupport p f) hS := by
      rw [hveq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hRmem)
    have hPv := NewtonPolygon.npVertices_on_hull (M2.valSupport p f) hS hPmem'
    have hRv := NewtonPolygon.npVertices_on_hull (M2.valSupport p f) hS hRmem'
    have hP1pos : 0 < P.1 := hhead0 P.1 (List.mem_map_of_mem hPmem)
    -- slope of the (P, R) side is ≥ 0
    have hslopele : (0 : ℚ)
        ≤ ((R.2 : ℚ) - (P.2 : ℚ)) / ((R.1 : ℚ) - (P.1 : ℚ)) := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hP1pos) with heq1 | hgt1
      · -- P sits at abscissa 1, height 0
        have hPv1 : (P.2 : ℚ) = 0 := by
          rw [hPv, ← heq1]
          push_cast
          exact h1
        apply div_nonneg
        · rw [hPv1, sub_zero]; exact Nat.cast_nonneg _
        · have : (P.1 : ℚ) < (R.1 : ℚ) := by exact_mod_cast hlt
          linarith
      · -- P sits at abscissa ≥ 2: convexity through (1, 0)
        have hcvx := NewtonPolygon.npHeight_convexOn (M2.valSupport p f) hS
          ((R.1 : ℕ) : ℚ)
        have hR1 : (1 : ℕ) ≤ R.1 := by omega
        have hx : (1 : ℚ) ∈ Set.Icc (0 : ℚ) ((R.1 : ℕ) : ℚ) :=
          ⟨by norm_num, by exact_mod_cast hR1⟩
        have hz : ((R.1 : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) ((R.1 : ℕ) : ℚ) :=
          ⟨Nat.cast_nonneg _, le_refl _⟩
        have hxy : (1 : ℚ) < ((P.1 : ℕ) : ℚ) := by exact_mod_cast hgt1
        have hyz : ((P.1 : ℕ) : ℚ) < ((R.1 : ℕ) : ℚ) := by exact_mod_cast hlt
        have hkey := hcvx.slope_mono_adjacent hx hz hxy hyz
        rw [← hPv, ← hRv, h1] at hkey
        refine le_trans (div_nonneg ?_ ?_) hkey
        · rw [sub_zero]; exact Nat.cast_nonneg _
        · linarith
    have hSideSlope : (⟨P.1, R.1, P.2, R.2⟩ : NewtonPolygon.Side).slope
        = ((R.2 : ℚ) - (P.2 : ℚ)) / ((R.1 : ℚ) - (P.1 : ℚ)) := rfl
    have hslopele' : (0 : ℚ) ≤ (⟨P.1, R.1, P.2, R.2⟩ : NewtonPolygon.Side).slope := by
      rw [hSideSlope]; exact hslopele
    exact Rat.num_nonneg.mpr hslopele'
  -- assemble: the negative-slope filter keeps exactly the anchor side
  have hfirstpos : decide ((⟨0, 1, v₀, 0⟩ : NewtonPolygon.Side).h < 0) = true := by
    rw [(c1_side_datum v₀).2.1]
    simp only [decide_eq_true_eq]
    omega
  have htailnil : ((((((1 : ℕ), (0 : ℕ)) :: w).zip w).map
      (fun pr => (⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : NewtonPolygon.Side))).filter
        (fun S => decide (S.h < 0))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro Sd hSd
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hSd
    simp only [decide_eq_true_eq]
    exact not_lt.mpr (htails pr hpr)
  have hslist : sideList f = NewtonPolygon.npSides (M2.valSupport p f) hS := by
    rw [sideList, dif_pos hS]
  rw [principalSideList, hslist, hsides, List.filter_cons, hfirstpos, if_pos rfl,
    htailnil]

/-- **H6-C1 CORE, (c1)-datum form**: at the Hensel configuration the corpus
order-≤ 1 read lists EXACTLY ONE datum — the (c1)-shape tuple
(e, h, ℓ, s, u) = (1, v₀, 1, 0, v₀), finite slope, v₀ = v(f₍₀₎).  This is the
§3.3(a) k′ = 0 record content: the unique length-1 side of N₁⁻(f). -/
theorem principalData_hensel_a0_one (f : Polynomial ℤ_[p])
    (hc0 : f.coeff 0 ≠ 0) (hv0 : 1 ≤ (f.coeff 0).valuation)
    (hc1 : f.coeff 1 ≠ 0) (hv1 : (f.coeff 1).valuation = 0) :
    principalData f
      = [⟨1, (f.coeff 0).valuation, 1, 0, (f.coeff 0).valuation, false⟩] := by
  have hdat : sideToDatum (⟨0, 1, (f.coeff 0).valuation, 0⟩ : NewtonPolygon.Side)
      = (⟨1, (f.coeff 0).valuation, 1, 0, (f.coeff 0).valuation, false⟩ :
          SideDatum) := by
    obtain ⟨he1, hh, hdeg⟩ := c1_side_datum (f.coeff 0).valuation
    simp only [sideToDatum, he1, hh, hdeg]
    simp
  rw [principalData, principalSideList_hensel_a0_one f hc0 hv0 hc1 hv1,
    List.map_cons, List.map_nil, hdat]

/-- **H6-C1 — `tREAD`'s conclusion VERBATIM at k′ = 0, order ≤ 1, non-vacuous
form** (§3.3(a) branch a₀ = 1 ∧ j₀ = 0): at a k′ = 0 seam (`H.nodes = []`)
with the Hensel configuration at the X-key, the order-≤ 1 datum's side list
at the terminal index is NONEMPTY and every listed side carries the (c1)
datum (1, v₀, 1, 0, v₀) — the NONEMPTY + ∀-SIDES shape of A7's `tREAD` row,
with the unique side's datum displayed. -/
theorem tREAD_conclusion_hensel_k0 (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ιb : ZMod p →+* ↥(Theta H).base) (ι0 : ZMod p →+* ↥((Theta H).fld 0))
    (hlen : (Theta H).slopes.length ≤ 1) (hk0 : H.nodes = [])
    (hc0 : f.coeff 0 ≠ 0) (hv0 : 1 ≤ (f.coeff 0).valuation)
    (hc1 : f.coeff 1 ≠ 0) (hv1 : (f.coeff 1).valuation = 0) :
    (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides H.nodes.length ≠ [] ∧
    ∀ S ∈ (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides H.nodes.length,
      (S.e, S.h, S.ℓ, S.s, S.u)
        = (1, (f.coeff 0).valuation, 1, 0, (f.coeff 0).valuation) := by
  have hps : (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides
      H.nodes.length = principalData f := by
    rw [hk0]
    simp [gmnDataOrder1]
  rw [hps, principalData_hensel_a0_one f hc0 hv0 hc1 hv1]
  refine ⟨List.cons_ne_nil _ _, ?_⟩
  intro S hS
  rw [List.mem_singleton] at hS
  subst hS
  rfl

/-- **H6-C1 rider — the ν-record glue**: any terminal record whose
(e, h, ℓ, s, u) are READ AS the (c1) datum satisfies `tREAD`'s conclusion
tuple-for-tuple at the k′ = 0 Hensel seam (the shape C0's
`terminalReadRecord` owes at a genuine seam, and the exact consumable for
the A7 row's ∀-SIDES clause). -/
theorem tREAD_shape_hensel_k0 (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ιb : ZMod p →+* ↥(Theta H).base) (ι0 : ZMod p →+* ↥((Theta H).fld 0))
    (hlen : (Theta H).slopes.length ≤ 1) (hk0 : H.nodes = [])
    (hc0 : f.coeff 0 ≠ 0) (hv0 : 1 ≤ (f.coeff 0).valuation)
    (hc1 : f.coeff 1 ≠ 0) (hv1 : (f.coeff 1).valuation = 0)
    (ν : ENodeData)
    (hν : (ν.e, ν.h, ν.ℓ, ν.s, ν.u)
      = (1, (f.coeff 0).valuation, 1, 0, (f.coeff 0).valuation)) :
    (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides H.nodes.length ≠ [] ∧
    ∀ S ∈ (gmnDataOrder1 f (Theta H) ιb ι0 hlen).principalSides H.nodes.length,
      (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u) := by
  obtain ⟨hne, hall⟩ :=
    tREAD_conclusion_hensel_k0 f H ιb ι0 hlen hk0 hc0 hv0 hc1 hv1
  exact ⟨hne, fun S hS => hν.trans (hall S hS).symm⟩

end UnitC1

end LeanUrat.Scaffold.HDischarge.H6
