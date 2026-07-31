/-
Unit R7-FILL  (queue item 13 EXECUTION, second half — the (†15) re-attempt, 2026-07-31)
[Asvin sign-off 2026-07-31, queue item 13: after the `OffsetPPin.total` re-key to
`HistoryCoherent` nodes (preferred option (ii), landed in PolPin.lean this round), the
charge is to RE-ATTEMPT `canPolicy`/`canPolicy_pin` (MovesD/TreeCan.lean:485,492 — the
census critical-path head, the D-group sorryAx source) and report exactly how far the
D-group opens.  OUTCOME: **REDUCED-COMPILED, NOT DISCHARGED** — this module is the
compiled reduction; the TreeCan sorries are UNTOUCHED (they remain the honest boundary).]

## What is proved here (0 sorry)

1. `CanRealizes` — the pin's five realizer laws bundled at ONE node (nonzero + forced
   (S6b) support + the D.10 digit/weight prescription at recenterings).  Lift-blind by
   construction (reads no `ν.lift`).
2. `canLiftOf` / `canPolicyC` — the CHOICE-BASED canonical policy: at each node, pick
   a `CanRealizes` witness if one exists (else 0).  `blind` is `rfl` (the choice
   proposition never reads the lift field).
3. `RunRealizerExists` — **THE ONE RESIDUAL LAW**, now a named Prop: at every
   recentering node of every `HistoryCoherent` history there EXISTS a `CanRealizes`
   realizer.  This is the (S6b′) content of PolPin's named HC-1 residue, in run-node
   vocabulary — the exact gap between the repaired pin and a compiled instance.
4. `canPolicyC_pin : RunRealizerExists p F → OffsetPPin (canPolicyC p F)` — **THE
   REDUCTION**: given (3), ALL FIVE pin laws are proved.  So the (†15) pair
   `canPolicy`/`canPolicy_pin` is fillable from `RunRealizerExists p (ZMod p)` alone
   (`canPolicy p := canPolicyC p (ZMod p)`, `canPolicy_pin p := canPolicyC_pin hex`).
5. `interior_recentering_unramified` + `interior_center_realizer_exists` — the
   COHERENCE-SUPPLIED half of (3): at every INTERIOR recentering node (i+1 < len),
   `IsRecenteringCore.base` forces the frame unramified (σ.e = 1) AND supplies a
   center realizer — the recorded lift itself (nonzero, in C_Φ, weight w(Φ), top
   digit = the recorded center).  The (†R7) forcing argument is thereby CONSISTENT
   with the repaired pin: on reachable interior nodes the realizer exists.

## Exactly how far the D-group opens (the charged report, in-file copy)

The R7/forge countermodel is CURED at the statement level: it now refutes only the
frozen `OffsetPPinBare` (bare-Node `total`), so `canPolicy_pin` is no longer
FALSE-AS-QUANTIFIED — it returns from refuted to OPEN, and every D-group consumer
binding `OffsetPPin pol` binds a satisfiable-looking interface again.  What remains
between HEAD and a sorry-free (†15) pair is `RunRealizerExists p (ZMod p)`, whose
unproved content splits as:
  (a) INTERIOR SUPPORT — the interior CR-witness (5) lacks only `CanRealizes`'s
      support clause: at a recentering (e = g = 1, `hspecRec`) the clause says the
      realizer is a MONOMIAL (singleton support), which `IsRecentering` does not
      record about `ν.lift` at frames with deg Φ > 1.  This is exactly PolPin's
      (S6b′) residue: the prescribed-digit realizer is monomial BY THE FORMULA, not
      by the Stage interface.  Owner HC-1 (lower-stage realizer export), unchanged.
  (b) THE LAST-NODE FLANK — a history's FINAL node carries no `IsRecenteringCore`
      record under bare `HistoryCoherent` (clause 4 needs i+1 < len); its landing
      law lives one predicate up (`JetSetup.landing`/`LandingKey`).  Deriving even
      the CR part there needs the (S6b) threshold law `wPrev Φ < h` (the probe's
      `centerRealizer_exists_of_unramified_threshold` displays the exact missing
      reachability ingredient) — or a countermodel at this flank would re-adjudicate
      the quantifier to the JetSetup carrier.  NAMED OPEN FLANK, recorded (not
      silent) in notes/QUEUE_EXECUTION_2026-07-31.md §Item-13.
So: D-group sorryAx count is UNCHANGED at HEAD (canPolicy/canPolicy_pin stay 2), but
the residue is now ONE compiled-named Prop (`RunRealizerExists`) instead of a refuted
universal, with its coherence-derivable half PROVED here.

moves_ref: note 4646–4651 (the ONE lift rule) + L1 note 4653–4667 (run-node totality)
+ D.10/`IsRecentering` (Moves/Defs.lean:271) + §B2-DEF D.5 (S6b)/(S6b′).
deps: PolPin (the repaired pin; brings MovesD.Defs, MovesC.Defs, Moves.Defs).
sketch: choice policy + field-by-field pin assembly + coherence destructuring.
difficulty: easy (the content is the reduction shape).  hypothesis_fields:
`RunRealizerExists` (the named residual law — hypothesis, never asserted).
-/
import Mathlib
import LeanUrat.MovesD.PolPin

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD

open Polynomial LeanUrat.Moves LeanUrat.MovesC

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The pin's realizer laws AT ONE NODE, bundled (lift-blind: no clause reads `ν.lift`):
nonzero + the (S6b) forced-class support geometry + the D.10 digit/weight prescription
at recenterings.  `OffsetPPin.Realizes`'s intended fiber, minus the policy tie. -/
def CanRealizes (ν : Node p F) (t : Polynomial ℤ_[p]) : Prop :=
  t ≠ 0 ∧
  (∃ j₀ : ℕ, (j₀ : ℤ) % (ν.e : ℤ) = (bezT ν.e ν.h * ν.gam) % (ν.e : ℤ) ∧
    ∀ j ∈ t.support, ∃ k : ℕ, k < ν.g ∧ j = j₀ + k * ν.e) ∧
  (ν.species = ReadSpecies.recentering →
    inC ν.σ.Φ t ∧ ν.σ.w t = ν.σ.w ν.σ.Φ ∧
      ν.σ.R t = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0)

open Classical in
/-- The CHOICE-BASED canonical lift: a `CanRealizes` witness where one exists, else 0.
Deterministic by construction (L1's "the digits are FUNCTIONS of the node data"). -/
noncomputable def canLiftOf (ν : Node p F) : Polynomial ℤ_[p] :=
  if h : ∃ t, CanRealizes ν t then h.choose else 0

/-- `canLiftOf` never reads the lift field: the choice proposition is definitionally
unchanged under a lift update (no `CanRealizes` clause mentions `ν.lift`). -/
theorem canLiftOf_blind (ν : Node p F) (t : Polynomial ℤ_[p]) :
    canLiftOf { ν with lift := t } = canLiftOf ν := rfl

/-- If a `CanRealizes` witness exists at ν, `canLiftOf ν` is one. -/
theorem canLiftOf_spec {ν : Node p F} (h : ∃ t, CanRealizes ν t) :
    CanRealizes ν (canLiftOf ν) := by
  unfold canLiftOf
  rw [dif_pos h]
  exact h.choose_spec

end

/-- **The choice-based canonical policy** — the strongest policy currently constructible
without the (S6b′) lower-stage export: pick the `CanRealizes` realizer where one exists. -/
noncomputable def canPolicyC (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] :
    CanonPolicy p F :=
  ⟨canLiftOf, canLiftOf_blind⟩

/-- **THE ONE RESIDUAL LAW** (the compiled name for what separates HEAD from a sorry-free
(†15) pair): at every recentering node of every `HistoryCoherent` history, a `CanRealizes`
realizer EXISTS.  Its coherence-derivable half is `interior_center_realizer_exists` below
(interior nodes, CR clauses); its open content is (a) the interior SUPPORT clause and
(b) the LAST-NODE flank — see the header report. -/
def RunRealizerExists (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ (H : History p F), LeanUrat.MovesC.HistoryCoherent H →
    ∀ (i : ℕ) (hi : i < H.nodes.length),
      (H.nodes[i]'hi).species = LeanUrat.MovesC.ReadSpecies.recentering →
      ∃ t, CanRealizes (H.nodes[i]'hi) t

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open LeanUrat.MovesC in
/-- **THE REDUCTION** (the (†15) re-attempt's yield): `RunRealizerExists` fills the WHOLE
repaired pin at the choice policy — all five laws.  `canPolicy p := canPolicyC p (ZMod p)`
and `canPolicy_pin p := canPolicyC_pin hex` discharge TreeCan's (†15) pair from this one
Prop; nothing else is missing. -/
noncomputable def canPolicyC_pin (hex : RunRealizerExists p F) :
    OffsetPPin (canPolicyC p F) where
  Realizes ν t := CanRealizes ν t ∧ t = canLiftOf ν
  total H hH i hi hν := ⟨canLiftOf_spec (hex H hH i hi hν), rfl⟩
  realizes_ne_zero ν t h := h.1.1
  support_forced ν t h := h.1.2.1
  realizes_unique ν t t' h h' := h.2.trans h'.2.symm
  digits_prescribed ν t h hν := h.1.2.2 hν

open LeanUrat.MovesC in
/-- The coherence-supplied UNRAMIFIEDNESS at interior recentering nodes: clause 4's
`IsRecenteringCore.base` (= `IsRecentering`) records `σ.e = 1` — the (†R7) parity
consequence holds ON REACHABLE INTERIOR NODES exactly as the probe predicted, so the
repaired `total` demands realizers only where the run's own geometry admits them. -/
theorem interior_recentering_unramified {H : History p F}
    (hH : HistoryCoherent H) {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hν : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering) :
    (H.nodes[i]'(by omega)).σ.e = 1 := by
  obtain ⟨-, -, -, h4⟩ := hH
  obtain ⟨hrec, -, -, -, -, -, -⟩ := h4 i hi
  exact (hrec hν).base.1

open LeanUrat.MovesC in
/-- The coherence-supplied CENTER REALIZER at interior recentering nodes: the node's OWN
recorded lift is nonzero, lives in C_Φ, carries the key weight, and reads the recorded
center — `IsRecentering`'s clauses 3–7 verbatim.  This is `RunRealizerExists`' CR content
at interior nodes; ONLY `CanRealizes`'s support clause (the (S6b′) monomial shape) is not
recorded by coherence.  (At the LAST node no `IsRecenteringCore` record exists at all —
the named open flank.) -/
theorem interior_center_realizer_exists {H : History p F}
    (hH : HistoryCoherent H) {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hν : (H.nodes[i]'(Nat.lt_of_succ_lt hi)).species = ReadSpecies.recentering) :
    ∃ t : Polynomial ℤ_[p], t ≠ 0 ∧ inC (H.nodes[i]'(Nat.lt_of_succ_lt hi)).σ.Φ t ∧
      (H.nodes[i]'(Nat.lt_of_succ_lt hi)).σ.w t
        = (H.nodes[i]'(Nat.lt_of_succ_lt hi)).σ.w (H.nodes[i]'(Nat.lt_of_succ_lt hi)).σ.Φ ∧
      (H.nodes[i]'(Nat.lt_of_succ_lt hi)).σ.R t
        = LaurentPolynomial.C (H.nodes[i]'(Nat.lt_of_succ_lt hi)).center
            * LaurentPolynomial.T 0 := by
  obtain ⟨-, -, -, h4⟩ := hH
  obtain ⟨hrec, -, -, -, -, -, -⟩ := h4 i hi
  obtain ⟨-, -, -, hinC, htne, hw, hR, -⟩ := (hrec hν).base
  exact ⟨(H.nodes[i]'(Nat.lt_of_succ_lt hi)).lift, htne, hinC, hw, hR⟩

end

end LeanUrat.MovesD

#print axioms LeanUrat.MovesD.canPolicyC_pin
#print axioms LeanUrat.MovesD.interior_recentering_unramified
#print axioms LeanUrat.MovesD.interior_center_realizer_exists
-- 
-- ═══ HK-06 WAVE NOTE (2026-07-31, task #44, wave executor) ═══
-- Scope of this dated note: the pre-wave reachability fence: the LAST-NODE FLANK note said a 
-- coherent history ending in a recentering over a ramified frame was 'blocked by the same HK22 wall 
-- pre-HK-06'. The HK-06 wave LANDED (task #44) and HC2/HK23_twoNodeGatePos.lean compiles the 
-- ramified-child gate — the flank's countermodel search is now LIVE (a 3-node extension of H₂ram 
-- by a recentering read is the natural target); the RunRealizerExists reduction itself is unaffected.
