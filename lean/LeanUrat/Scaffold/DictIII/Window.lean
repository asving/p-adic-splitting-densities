/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.MovesD.R7_polFillReduction
import LeanUrat.HC2.UE_vtxUpper

/-!
# Scaffold/DictIII/Window — (M6c) + WGEO + REAL≡ (BP_III §1.7)

E-phase transcription of `lean/blueprints/BP_III.md` §1.7.  This file currently
holds unit III-T14m (`M6ABHyps` + `M6cHyps`, statement only — the named
M6a/M6b/M6c hypothesis rows that `realEquiv_of_m6` (units III-T14a/b) will
consume; REV2 finding 14).  Source of record: O1thr §2.5 REAL≡.  HYPOTHESIS
rows, not axioms.

Status at hand-off (unit III-T14m, 2026-08-01): `M6cHyps` landed VERBATIM;
`M6ABHyps` is BLOCKED on a statement defect — record below.
-/

namespace LeanUrat.Scaffold.DictIII

/-! ## Unit III-T14m — `M6ABHyps` (BP_III §1.7): BLOCKED on a statement defect
in both rows

The verbatim blueprint statement is preserved in the commented block below; it
is NOT weakened or partially landed (retargeting the `CanRealizes` application
would be a statement change).  Status at hand-off (2026-08-01):

* -- BLOCKED(III-T14m): rows `m6a` and `m6b` apply the corpus predicate as
  `MovesD.CanRealizes p F n f H`.  BP_III §3's corpus map pins
  `MovesD.CanRealizes` to `LeanUrat.MovesD.CanRealizes`
  (`MovesD/R7_polFillReduction.lean:85`), whose signature is
  `CanRealizes {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (t : Polynomial ℤ_[p]) : Prop`
  — `p`,`F` are IMPLICIT and the explicit slots are ONE node ν plus ONE
  polynomial t (the pin's realizer laws AT ONE NODE), not (p, F, n, f, H).
  Exact compiler error at both displayed rows (Lean 4.31, this pin,
  2026-08-01):
    `Application type mismatch: The argument p has type ℕ but is expected to
     have type MovesC.Node ?m.9 ?m.11 in the application
     MovesD.CanRealizes p`.
  The rows need a blueprint-level repair — how the history-level predicate
  "f can be realized along H" is assembled from the corpus one-node
  `CanRealizes` (e.g. which nodes of `H.nodes` carry a witness, and where the
  degree bound n enters) — which is fenced above this unit's authority.

```
structure M6ABHyps (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop where
  m6a : ∀ {n : ℕ} {f : Polynomial ℤ_[p]} {H : MovesC.History p F},
    MovesJ.ReadsOf p F n f H → MovesD.CanRealizes p F n f H
  m6b : ∀ {n : ℕ} {f : Polynomial ℤ_[p]} {H : MovesC.History p F},
    MovesD.CanRealizes p F n f H → H.nodes ≠ []
```
-/

/-- Unit III-T14m (BP_III §1.7, transcribed VERBATIM): the (M6c) supply row —
the general residual-structure package `GRB` (unit III-H1) is exactly what the
REAL≡ equivalence consumes on the M6c side.  Named hypothesis row exposing the
M6c conditionality of `realEquiv_of_m6` (units III-T14a/b); HYPOTHESIS, not
axiom.  Source: O1thr §2.5 REAL≡. -/
def M6cHyps (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop :=
  GRB p F

/-! ## Unit III-T11b — BLOCKED on a missing blueprint statement (record, 2026-08-01)

-- BLOCKED(III-T11b): the blueprint contains NO typed Lean statement to transcribe.
BP_III §1.7 (line 524) displays the unit's theorem as

  theorem m6c_beyondWindow …

— an ellipsis, not Lean.  Transcribed verbatim, the exact compiler error
(Lean 4.31, this pin) is:

  error: expected token          -- at the `…` character, col 25

No other display exists: the unit table row (BP_III line 791), D-R4 (line 973),
and REV2 finding 15 (line 996) describe the unit only in prose ("general
(M6c)(i) statement under `GRB` and `OL2min`; fire the named higher-order
rows").  REV2 finding 1 replaced the §1 ellipses for structures/definitions,
but §1.7's three theorems (`m6c_beyondWindow`, `m6c_noPhantom`, `wgeo`) were
left elided.  Composing the general statement here — choosing the binders for
"state on f", "harvested child", "(R1) at ALL slots", the window vocabulary,
and how `GRB`/`OL2min` (Hyps.lean, landed) enter as hypotheses — would be
architect-phase statement design, which is fenced (statements are fences;
statement invention = statement change).

Independently blocking: dependency III-T11a (the `e′ = 1` degree-one anchor
statement this unit generalizes) has NOT landed anywhere in the corpus at
hand-off (no `m6c`-named declaration outside this record; this file holds only
III-T14m's `M6cHyps` — its `M6ABHyps` sibling is itself BLOCKED, record
above), so there is also no landed anchor signature to re-key under the
GRB/OL2min rows.

Needs a blueprint-level repair: the architect supplies the typed general
(M6c)(i) signature (or T11a lands first and the architect rules how its
`e′ = 1` hypothesis is replaced by the `GRB p F` + `OL2min f c D` rows). -/

/-! ## Unit III-T15 — Corollary VTX wrapper (BP_III §2 Wave 3 row T15; src O1thr §2.5 VTX)

VERBATIM re-export of the corpus theorem `LeanUrat.MovesJ.UE.vtx_htUpper_div`
(`HC2/UE_vtxUpper.lean`) — the ℚ display `vhtx ≤ γ/e₀ = I` of Corollary VTX's
(N4)-upper band at the recorded read's data.  Per REV2 finding 26, the SOURCE
signature is displayed by the `#check` below (typechecked at elaboration), the
TARGET signature is the wrapper's own displayed statement (transcribed
character-for-character from the source, `HC2/UE_vtxUpper.lean:153-162`), and
the proof is the bare exact application — so definitional equality of the two
signatures is machine-confirmed, which is what licenses the word "verbatim".
Zero new proof debt; carried hypotheses unchanged (the honest conditionality:
`StageCoreL` tower provenance, STRICT read steepness, non-recentering species).
-/

section UnitIIIT15

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1
  LeanUrat.MovesJ

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

-- SOURCE signature display + typecheck (REV2 finding 26 gate).
#check @LeanUrat.MovesJ.UE.vtx_htUpper_div

/-- **Unit III-T15 (Corollary VTX, the ℚ display `vhtx ≤ γ/e₀ = I`)** — verbatim
re-export of `UE.vtx_htUpper_div` under the scaffold-facing name: at a coherent
`ReadsOf` record with a non-recentering, strictly steep read `i` of tower
provenance, the vertex coefficient's own-frame height is at most the read
intercept `gam/e` — the exact (R5)-record bound of the (N4)-UPPER band
(O-1thr rev 3 §2.5).  Proof: exact application of the source theorem. -/
theorem vtx_htUpper_div {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    ((H.nodes[i]'(by omega)).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ)
      ≤ ((H.nodes[i]'(by omega)).gam : ℚ) / ((H.nodes[i]'(by omega)).e : ℚ) :=
  UE.vtx_htUpper_div h i hi1 hsp hσL hsteep B Nd hdev

end UnitIIIT15

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-T15 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.vtx_htUpper_div
