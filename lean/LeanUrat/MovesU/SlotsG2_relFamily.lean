/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG1_cinterface

/-!
# IB-G2 — Slot_rel1 + Slot_rel2a/b/d/e FORMULATION SKELETONS (bridge BP1, §3.8)

E-phase skeletons per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 + §4
group G (IB-G2: "Slot_rel1 + Slot_rel2a/b/d/e formulations over G1. ADJ→H,
statement-only (5 displayed Props; the p^N-torsion trap documented)") and
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q5: proceed now,
statement-only, Codex audit before consumers).

THE RESERVED PARAMETERS BEING TYPED (U10_theoremU.lean:67–69, verbatim):
"`rel1`, `rel2a`, `rel2b`, `rel2d`, `rel2e`, `rel3` — CL-8's six REL rows (owner
[2r]; the typed (EQ-2) face is `KT.cl8_eq2`; (e)'s operative trace is the carried
`C.chain.legs_read`)."  These are five of the thirteen WAVE-4 BOUNDARY bare-Prop
parameters of `theoremU` — UNPINNED (True-instantiable) pending these carriers.
The parameters STAY in `theoremU`'s signature (statement fence); IB-G13's
`theoremU_bridged` instantiates them at the Props below, call-site only.

E-PHASE DIVISION OF LABOR (why the bodies are `sorry`): the G-units are ADJ→H
because "these were left bare precisely because faithful self-contained typing
FAILED once — MovesR adjudication #1" (§3.8) and R9 mandates statement-only
formulation + closure manifest + non-vacuity falsifier + CODEX AUDIT before any
consumer.  The E-phase deliverable is therefore the BINDER SURFACE (each slot a
Prop over the G1 `CInterface` carrier, per the blueprint's "parameterize by the
MovesR re-architecture's CInterface carrier") + the formulation targets below;
the DISPLAYED Prop bodies are the H-phase deliverable, Codex-audited per Q5.
Filling a body here is a statement-design event, not a proof — the H-prover must
route it through the audit gate, never silently.

FORMULATION TARGETS (deps: IB-G1; owner [2r]; note display CL-8):
* `Slot_rel1` — REL.1, the base-change ledger clause at δ: the O_δ-re-based
  theory's ledger (§A, §B1, §B2-DEF, §C through Theorem C(a)/(b) with
  C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM) holds at the carrier `CI` —
  the parked draft's `CStatements`-shaped record, RE-TYPED per the wave-5
  resumption charge (campaign ledger, MovesR PARKED entry + MOVESR_AUDIT_FABLE3):
  (i) TYP's additive object = the LEVEL-SET-DIGITS → GRADED-PIECE COMPOSITE
  `(y_c)_c ↦ CI.G.inγ γ (CI.slotCoeff H B y)` on L_γ(B)-supported assignments
  (MOVES 3801–07, 9401–04) — NEVER `CI.jet`-additivity on box points (the
  p^N-torsion trap: as the parked draft typed it, the clause is group-
  theoretically IMPOSSIBLE and the intended instance would FALSIFY REL.1);
  (ii) alphabets priced on the slot-image SPAN (TYP(b) 3815–21; F₉ a = 2 check);
  (iii) `CI.floorB` linked to `CI.lines` through `CI.blockEdge` by the staircase
  equation (the F3-3 repair — the carrier half landed at IB-G1 resolution R-3);
  (iv) the counting clause (REL.1-b) at the DEFINED `CI.count` (FF2):
  `(CI.count H Z N : ℚ) = (qq p δ)^(n·N) · ∏ᵢ vol(E_fresh νᵢ) · vol(Z)` for
  N ≥ Nmin H Z.  The worked δ = 1 re-key pattern is HC1/DefsCar.lean.
* `Slot_rel2a` — REL.2(a), the branch continuation-map package: the six
  sub-deliverables (a1) domain+measurability, (a2) target integrality
  d_j^rel = d_j/δ_j^rel, (a3) embedding/Teichmüller-lift convention, (a4) the map
  Θ_j, (a5) frame compatibility with unitriangular anchors both sides, (a6) the
  per-read dictionary preserving shape/anchor/side with transported residue data
  (the parked REL2a1–a6 shapes are raw material; their `Setting`-side binder
  design is part of the H-phase formulation).
* `Slot_rel2b` — REL.2(b), normalization/Jacobian: for every REL.1-measurable
  continuation event W over O_{δ_j}, μ(Θ_j⁻¹ W │ Σ_c) = vol_{O_{δ_j}}(W), guarded
  by μ(Σ_c) > 0, with the Θ-pullback required IN the ambient event algebra, and
  the REL.1 conditionality displayed per site (the parked `REL2b_linked` shape).
* `Slot_rel2d` — REL.2(d), lift-policy compatibility: the acceptance-criterion
  commutative square `nodeCorr (T_can(f)) = T_can^{O_δ}(Θ f)` with the node-data
  correspondence SPECIFIED (species word preserved, reads transported through the
  (a6) dictionary, τ-verdicts preserved, (EQ-2) alphabet wiring constrained by
  `posOf_letter`) + the prescribed-subtree identification.
* `Slot_rel2e` — REL.2(e), β-identification (e1)–(e5): REL.1-side states with the
  read-compatible dictionary, [3]'s table in its own keying, e_j fixed per branch,
  determination of the prescribed subtree, and MASS = ENTRY at the REL.1 vol —
  with `tableConv`/`consumed` as PARAMETERS supplied by [3]/MovesS (the CF13/CF14
  vacuity repairs), never chosen by the instance.

NON-VACUITY DUTY (IB-G11a): each filled Prop must be FALSE for a degenerate
instance the note would reject — one compiled falsifier per slot.
CLOSURE MANIFEST DUTY (IB-G12): every identifier in each displayed Prop → its
built decl path, grep-verified.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
H-PHASE RESOLUTIONS FOR `Slot_rel1` (2026-07-30, cluster BP1-P10-slots; the
re-typing executes the recorded resumption charge against the parked draft's
`CStatements` (MOVESR_LEAN_BLUEPRINT_2026-07-28.md 631–647) with the
MOVESR_AUDIT_FABLE3 repairs; every resolution FLAGGED for the Q5 Codex audit):
* (r-F3-1, CRITICAL repair) TYP conjunct 1: the jet-additivity clause
  (`jet H (f+g) i = jet H f i + jet H g i`) is DELETED — group-theoretically
  impossible (O_δ has p^N-torsion; an additive jet factors through mod p) and not
  the note's claim.  REPLACED by the note's own additive object, the
  LEVEL-SET-DIGITS → GRADED-PIECE COMPOSITE (MOVES 3801–07, 9401–04): on
  L_γ(B)-supported digit assignments, `y ↦ CI.G.inγ γ (CI.slotCoeff H B y)` is
  additive in the digit tuple.  The worked δ = 1 pattern is
  `HC1.Tower.typComposite` (DefsCar.lean:194).
* (r-F3-2, CRITICAL repair) TYP conjunct 2: the alphabet is priced on the
  SLOT-IMAGE SPAN in the graded piece (`AddSubgroup.closure` of the
  single-coordinate composite images), NEVER on `Set.range (jet H · i)` — the
  audit's own displayed faithful form, verbatim (the F₉ a = 2 instance is the
  check).  δ = 1 pattern: `HC1.Tower.alphabet` (DefsCar.lean:200).
* (r-F3-3, CRITICAL repair) LST clause (ii): `floorB` is PINNED by the staircase
  equation `floorB H B = (lines H (top read)).at (blockEdge H B)` on
  factor-interior blocks (guard = the display's "there", MOVES 3650–51/3717–22),
  through the G1 carrier's R-3 `blockEdge` field; the constancy clause
  (`floorC = floorB` on the interior) is kept.  δ = 1 pattern:
  `HC1.TowerRealizable.floorB` (DefsCar.lean:266).
* (r-G3-1) SecB1's Coeff-LEVEL slotCoeff additivity is DROPPED (in the engine
  ring, unit lifts are not additive — the audit's gap; the HC1 worked instance's
  `slotCoeff` is a Teichmüller-style expansion, NOT additive at Coeff level).
  The note's additivity is carried at the graded-piece level by the (r-F3-1)
  composite clause; SecB1 keeps the stage-carrier laws.
* (r-G3-2) The (i-b)/(i-c) quantification over all `B : ℕ` is kept with the
  draft's recorded convention (off-window blocks ride the `w 0 = ⊤`/`slotCoeff 0`
  convention) — recorded, not silently scoped.
* (r-G3-3) DOM is typed via its INPUT package `MovesC.DomData` (steeper chain +
  vertex entry), per the parked draft + the D8 declaration; `interiorEnd` as one
  bound for all i ≤ kIdx is benign (interiors nest) — recorded.
NON-VACUITY (IB-G11a's duty): FALSE at a degenerate CI violating e.g. the C.1
pricing (vol of a locus ≠ the per-pinned-digit product) or the (r-F3-2) span
cardinality.
-/

namespace LeanUrat.MovesU

open MovesRBase

open scoped Classical

/-- IB-G2 slot 1/5 — **`Slot_rel1`** (CL-8 REL.1, owner [2r]): the O_δ-re-based
theory's full ledger clause at the CInterface carrier `CI` — the re-typed
`CStatements` record (see the file header's formulation target, incl. the
p^N-torsion re-typings (i)–(iii) and the FF2 counting clause (iv)).  H-phase
fills the displayed Prop; Codex audit before any consumer (Q5). -/
def Slot_rel1 {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {δ : ℕ+} {n : ℕ} (CI : CInterface p Sp AD δ n) : Prop :=
  -- §A re-based: base tower shape over F_δ:
  (∀ H, (CI.tower H).BaseLaws) ∧
  -- §B1 re-based (r-G3-1: stage-carrier laws only; the additive law rides the
  -- graded-piece composite clause below):
  (∀ H, (CI.tower H).StageCarrierLaws) ∧
  -- §B2-DEF re-based: the D.0 climb over the new base:
  (∀ H, (CI.tower H).ClimbLaws) ∧
  -- Theorem C(a): classifier locus = jet-preimage of the digit-system locus:
  (∀ H Z, CI.SHZ H Z
      = (fun f => CI.jet H f) ⁻¹' {x | (CI.digitLocus H Z).IsSolution x}) ∧
  -- Theorem C(b) = (REL.1-b), LHS the DEFINED count (FF2):
  (∀ (H : CI.C.Hist) (Z : CI.C.Locus H) (N : ℕ), CI.C.Nmin H Z ≤ N →
    (CInterface.count p CI H Z N : ℚ) = (qq p δ : ℚ) ^ (n * N) *
      ((∏ i ∈ Finset.range (CI.C.kIdx H + 1), CI.C.V.vol (CI.C.freshEvent H i)) *
        CI.C.V.vol (CI.C.locusEvent H Z))) ∧
  -- C.0.5 + PIN-WELLDEF: unitriangular transports; pin statistics frame-invariant
  -- (cardinality AND status AND the aDim ledger weights):
  (∀ H (F F' : CI.Frame H), MovesC.IsUnitriangular (CI.T H F F') ∧
    ∀ Z, (CI.pinnedIn H F Z).card = (CI.pinnedIn H F' Z).card ∧
      Multiset.map (CI.pinStatus H F Z) Finset.univ.val
        = Multiset.map (CI.pinStatus H F' Z) Finset.univ.val ∧
      (CI.pinnedIn H F Z).val.map (CI.aDim H)
        = (CI.pinnedIn H F' Z).val.map (CI.aDim H)) ∧
  -- C.1: locus mass = the per-pinned-digit product of attainable-alphabet inverses:
  (∀ H (F : CI.Frame H) Z, CI.C.V.vol (CI.C.locusEvent H Z)
      = ∏ i ∈ CI.pinnedIn H F Z, ((p : ℚ) ^ (CI.aDim H i))⁻¹) ∧
  -- C.1.5's (ZC) invariant:
  (∀ H F F' Z, CI.zcStat H F Z = CI.zcStat H F' Z) ∧
  -- Lemma LST (i-a)/(i-b)/(i-c) + (ii) with the r-F3-3 staircase pin + (iii):
  (∀ H : CI.C.Hist,
    (∀ i, CI.G.w (CI.mono H i) = ((CI.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ (B : ℕ) (x : Fin (CI.mOf H) → ↥(Fsub p δ)),
      CI.G.w (CI.slotCoeff H B x) = (Finset.univ.filter fun i =>
        CI.blkOf H i = B ∧ x i ≠ 0).inf fun i => ((CI.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ (γ : ℚ) (B : ℕ) (x y : Fin (CI.mOf H) → ↥(Fsub p δ)),
      (∀ i, CI.blkOf H i = B → CI.ht H i = γ → x i = y i) →
      CI.G.inγ γ (CI.slotCoeff H B x) = CI.G.inγ γ (CI.slotCoeff H B y)) ∧
    (∀ B : ℕ, CI.interiorB H B →
      CI.floorB H B = (CI.lines H (CI.C.kIdx H)).at (CI.blockEdge H B)) ∧
    (∀ i, CI.interiorB H (CI.blkOf H i) → CI.floorC H i = CI.floorB H (CI.blkOf H i)) ∧
    (∀ B, CI.interiorB H B →
      CI.floorSet H B = {i | CI.blkOf H i = B ∧ CI.ht H i ≤ CI.floorB H B} ∧
      ∀ (γ' : ℚ), CI.floorB H B < γ' →
        ∀ i, CI.blkOf H i = B → CI.ht H i = γ' → i ∉ CI.floorSet H B)) ∧
  -- Lemma TYP, RE-TYPED (r-F3-1: the level-set-digits → graded-piece composite is
  -- additive in the digit tuple):
  (∀ (H : CI.C.Hist) (B : ℕ) (γ : ℚ) (x y : Fin (CI.mOf H) → ↥(Fsub p δ)),
    (∀ i, x i ≠ 0 → CI.blkOf H i = B ∧ CI.ht H i = γ) →
    (∀ i, y i ≠ 0 → CI.blkOf H i = B ∧ CI.ht H i = γ) →
    CI.G.inγ γ (CI.slotCoeff H B (x + y))
      = CI.G.inγ γ (CI.slotCoeff H B x) + CI.G.inγ γ (CI.slotCoeff H B y)) ∧
  -- Lemma TYP graded leg, RE-TYPED (r-F3-2: the alphabet = the slot-image SPAN in
  -- the graded piece, priced at p^{a_δ}):
  (∀ (H : CI.C.Hist) (i : Fin (CI.mOf H)),
    Nat.card ↥(AddSubgroup.closure (Set.range fun y : ↥(Fsub p δ) =>
      CI.G.inγ (CI.ht H i) (CI.slotCoeff H (CI.blkOf H i) (Pi.single i y))))
      = p ^ CI.aDim H i) ∧
  -- Lemma DOM (r-G3-3: the displayed input package, base-free):
  (∀ H, ∀ i ≤ CI.C.kIdx H, MovesC.DomData (CI.lines H) i (CI.interiorEnd H))

/-!
BLOCKED RECORD — `Slot_rel2a`/`Slot_rel2b`/`Slot_rel2d`/`Slot_rel2e`
(2026-07-30, cluster BP1-P10-slots; honest sorries per the bounded-repair rule;
full analysis in the cluster report).  The H-phase attempt found NO faithful
CI-relative closure of the branch-site (`Setting`-shaped) binder:
* ∀-CLOSURE over abstract sites+packages is FALSE AT EVERY CI — a junk site
  (Dirac-valued `condMass` at a point of a genuine event algebra, constant Θ)
  satisfies every law of the parked REL2a1–a6 bundle, and REL.2(b)'s pricing
  fails against ANY cylinder-pinned `BoxVol` (two disjoint cylinders cannot both
  be priced by a two-valued conditional).  A slot false at the intended instance
  is an F3-1-class faithfulness failure.
* ∃-CLOSURE is True-instantiable at EVERY CI with a genuine `BoxVol` — the
  identity site (Cont := CI's box, condMass := CI.C.V.vol, Θ := id) satisfies
  (a1)–(a6) + (b) outright, killing the wave-2 falsifier duty entirely.
* The middle road (sites tied to an AMBIENT CInterface with `Slot_rel1`
  conditionality) still leaves Θ/the trees/the β-tables pinned by NOTHING built:
  the recentering vocabulary, prescribed-subtree carriers, and [3]-table exports
  the parked draft binds (`Setting`/`REL2d`/`tableConv`/`consumed`) have no
  in-corpus carriers, and re-inventing them here is a G1-scale carrier-layer
  design event — exactly the fence-scale move Q5's audit gate exists to catch.
DISPOSITION: the four bodies stay honest sorries; the site-carrier layer (or a
ratified alternative closure) is an orchestrator adjudication — surfaced, never
improvised (the rel3 escalation path's sibling; REVISION 2 finding 10's logic
applies to the whole REL.2 family).
-/

/-- IB-G2 slot 2/5 — **`Slot_rel2a`** (CL-8 REL.2(a), owner [2r]): the branch
continuation-map package, six sub-deliverables (a1)–(a6) — all six or nothing
(the parked bundle discipline).  Same carrier as `Slot_rel1`; the branch-side
(`Setting`-shaped) data is bound INSIDE the Prop (H-phase design). -/
def Slot_rel2a {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {δ : ℕ+} {n : ℕ} (CI : CInterface p Sp AD δ n) : Prop :=
  sorry

/-- IB-G2 slot 3/5 — **`Slot_rel2b`** (CL-8 REL.2(b), owner [2r]): the
normalization/Jacobian pricing μ(Θ⁻¹W │ Σ_c) = vol_{O_δ}(W) on REL.1-measurable
events, positive-cell guarded, REL.1-conditionality displayed per site. -/
def Slot_rel2b {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {δ : ℕ+} {n : ℕ} (CI : CInterface p Sp AD δ n) : Prop :=
  sorry

/-- IB-G2 slot 4/5 — **`Slot_rel2d`** (CL-8 REL.2(d), owner [2r]): lift-policy
compatibility — the commutative square with the SPECIFIED node-data
correspondence (word/reads/verdicts preserved; (EQ-2) wiring constrained) + the
prescribed-subtree identification (without which (SIB-Oδ) is ill-typed). -/
def Slot_rel2d {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {δ : ℕ+} {n : ℕ} (CI : CInterface p Sp AD δ n) : Prop :=
  sorry

/-- IB-G2 slot 5/5 — **`Slot_rel2e`** (CL-8 REL.2(e), owner [2r]): the
β-identification (e1)–(e5) with `tableConv`/`consumed` as [3]/MovesS-supplied
PARAMETERS (CF13/CF14 — instance-chosen versions were the audited vacuity)
and MASS = ENTRY priced at the REL.1 vol. -/
def Slot_rel2e {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {δ : ℕ+} {n : ℕ} (CI : CInterface p Sp AD δ n) : Prop :=
  sorry

end LeanUrat.MovesU
