/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesSp.Defs

/-!
# MovesSp/DefsEnum — Bool reflection layer + the generated enumeration

E-phase transcription of `lean/notes/MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` §3 (rev 5).
Definitions only, no `sorry`. Every n = 3 / n = 1 `decide` target routes through THESE
Bool functions (literal Bool transcriptions of `Coherent`/`Budget`/`RootAdmissible`/
`SuccStep`) — `native_decide` is BANNED corpus-wide (axiom fence).

[REV 4, Codex-6] BOOL ROUTING CONVENTIONS, binding on every decide target:
  list membership   → `l.contains x`  (BEq Species := instBEqOfDecidableEq)
  ℕ-inequalities    → `decide (a ≤ b)`
  Option tests      → `o.isSome` / `o == some v`
NEVER `(P : Bool)` on a Prop — Lean 4 has no Prop→Bool coercion.
(The two ambient Prop atoms — ≤ on ℕ, membership via DecidableEq — enter through
`decide (…)`; the (G4)/(B4) selection clauses' unbounded ∀ is handled by `match`
on `s.sel`, per the blueprint §1.1 honest-decidability note.)
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-! ### The generated enumeration (blueprint §3; feeds every n = 3 `decide`) -/

/-- All compositions of `span` (positive parts, ordered). compEnum 0 = [[]].
Recursion on span: first part k + 1 ∈ [1, span], then the rest. -/
def compEnum : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 =>
      (List.range (n + 1)).flatMap fun k =>
        (compEnum (n - k)).map fun c => (k + 1) :: c
decreasing_by omega

/-- Underlying LIST enumeration for `lamEnum`: all NONDECREASING (by pair index
k ↦ (k / bound + 1, k % bound + 1)) lists of pairs (g, μ), 1 ≤ g, μ ≤ bound, with
Σ g·μ = the first argument; `lo` = least allowed pair index (canonical sorted
representatives — each multiset appears once). -/
def lamEnumAux (bound : ℕ) : ℕ → ℕ → List (List (ℕ × ℕ))
  | 0, _ => [[]]
  | w + 1, lo =>
      ((List.range (bound * bound)).drop lo).flatMap fun k =>
        let g := k / bound + 1
        let μ := k % bound + 1
        if g * μ ≤ w + 1 then
          (lamEnumAux bound (w + 1 - g * μ) k).map fun l => (g, μ) :: l
        else []
decreasing_by
  have : 0 < (k / bound + 1) * (k % bound + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  omega

/-- All multisets of pairs (g, μ), 1 ≤ g, μ ≤ bound, with Σ g·μ = weight. -/
def lamEnum (bound weight : ℕ) : List (Multiset (ℕ × ℕ)) :=
  (lamEnumAux bound weight 0).map fun l => (l : Multiset (ℕ × ℕ))

/-- Generated candidates: for tag/D/w/W/e/s0/ell in dependent bounds
(D, w ∈ [1, n]; W ∈ [1, n/D] per (B3); e ∈ [1, W]; ℓ ∈ [1, W/e]; s₀′ ∈ [0, W − e·ℓ]),
lam ∈ lamEnum n ℓ, sel ∈ none :: (lam's entries mapped some), flanks ∈ compEnum of
their (G1) spans; a := s0/e, d := ell + 1, slots := Finset.Icc a (a + ell) COMPUTED
(coherent-by-construction on (G2)/(G3)). A SUPERSET of the coherent+admissible tuples
(Sp.speciesEnumComplete); duplicate sel candidates from repeated λ-factors are
harmless [REV 2, F16]. -/
def speciesEnum (n : ℕ) : List Species :=
  [Tag.root, Tag.postInc, Tag.postRec].flatMap fun tag =>
  (List.range n).flatMap fun D0 =>
  (List.range n).flatMap fun w0 =>
  (List.range (n / (D0 + 1))).flatMap fun W0 =>
  (List.range (W0 + 1)).flatMap fun e0 =>
  (List.range ((W0 + 1) / (e0 + 1))).flatMap fun ell0 =>
  (List.range ((W0 + 1) - (e0 + 1) * (ell0 + 1) + 1)).flatMap fun s0 =>
  (lamEnumAux n (ell0 + 1) 0).flatMap fun (lamL : List (ℕ × ℕ)) =>
  (none :: lamL.map some).flatMap fun sel =>
  (compEnum s0).flatMap fun lf =>
  (compEnum ((W0 + 1) - s0 - (e0 + 1) * (ell0 + 1))).map fun rf =>
    ⟨tag, D0 + 1, w0 + 1, W0 + 1, e0 + 1, s0, ell0 + 1, s0 / (e0 + 1), ell0 + 2,
     Finset.Icc (s0 / (e0 + 1)) (s0 / (e0 + 1) + (ell0 + 1)),
     Multiset.ofList lamL, sel, lf, rf⟩

/-! ### The Bool reflection layer (blueprint §1.2 / §3; soundness iffs = group A) -/

/-- Bool transcription of `WellTyped`. -/
def wellTypedB (s : Species) : Bool :=
  decide (1 ≤ s.D) && decide (1 ≤ s.w) && decide (1 ≤ s.W) && decide (1 ≤ s.e) &&
    decide (1 ≤ s.ell) && decide (∀ gm ∈ s.lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2)

/-- Bool transcription of `Coherent` ((G1)–(G4)+(G6)); the (G4) selection clause
`match`es on `s.sel` (blueprint §1.1 — no Prop-side Decidable needed). -/
def coherentB (s : Species) : Bool :=
  wellTypedB s &&
  -- (G1)
  (s.lflank.all fun x => decide (1 ≤ x)) && decide (s.lflank.sum = s.s0) &&
    decide (s.s0 + s.wraw + s.rflank.sum = s.W) &&
    (s.rflank.all fun x => decide (1 ≤ x)) &&
  -- (G2)
  decide (s.a = s.s0 / s.e) &&
  -- (G3)
  decide (s.slots = Finset.Icc s.a (s.a + s.ell)) && decide (s.d = s.ell + 1) &&
  -- (G4)
  decide ((s.lam.map fun gm => gm.1 * gm.2).sum = s.ell) &&
    (match s.sel with
     | none => true
     | some gm => decide (gm ∈ s.lam)) &&
  -- (G6)
  ((s.sel == none) == (s.W == 1))

/-- Bool transcription of `Budget` ((B1)–(B5)); the (B4) clause `match`es on `s.sel`. -/
def budgetB (n : ℕ) (s : Species) : Bool :=
  decide (s.D ≤ n) && decide (s.w ≤ n) &&
  -- (B3)
  decide (s.s0 + s.wraw ≤ s.W) && decide (s.a + s.ell ≤ s.W) &&
    decide (s.d ≤ s.wraw + 1) && decide (s.W ≤ n / s.D) &&
  -- (B4)
  (match s.sel with
   | none => true
   | some gm => decide (gm.1 * gm.2 ≤ s.ell)) &&
  -- (B5, census anchor)
  decide (s.e ≤ n) && decide (s.ell ≤ n) && decide (s.s0 ≤ n) && decide (s.d ≤ n + 1) &&
    decide (s.W ≤ n) && decide (∀ gm ∈ s.lam, gm.1 ≤ n ∧ gm.2 ≤ n) &&
    decide (s.e ≤ s.wraw) && decide (s.a ≤ (s.W - s.wraw) / s.e)

/-- Bool transcription of `RootAdmissible`. -/
def rootAdmissibleB (n : ℕ) (s : Species) : Bool :=
  (s.tag == Tag.root) && (s.D == 1) && (s.w == 1) && (s.W == n) &&
    coherentB s && budgetB n s

/-- Bool transcription of `SuccStep` (the `StageLaws` half by `match` on `s.sel`,
then target coherence + budget). -/
def succStepB (n : ℕ) (s s' : Species) : Bool :=
  (match s.sel with
   | none => false
   | some gm =>
       (s'.D == s.e * gm.1 * s.D) && (s'.w == gm.1 * s.w) && (s'.W == gm.2) &&
       ((s'.tag == Tag.postInc) == decide (2 ≤ s.e * gm.1)) &&
       ((s'.tag == Tag.postRec) == ((s.e == 1) && (gm.1 == 1)))) &&
  coherentB s' && budgetB n s'

end LeanUrat.MovesSp
