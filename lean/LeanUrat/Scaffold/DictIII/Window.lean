/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.MovesD.R7_polFillReduction
import LeanUrat.HC2.UE_vtxUpper
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

/-! ## Unit III-T14b — `realEquiv_of_m6` forward direction + biconditional
assembly: BLOCKED on the SAME statement defect, in the unit's OWN conclusion

The verbatim blueprint statement (BP_III §1.7) is preserved below; it is NOT
weakened or partially landed.  Status at hand-off (2026-08-01):

* -- BLOCKED(III-T14b): TWO independent grounds, verified by transcribing the
  displayed statement verbatim into a scratch module (Lean 4.31, this pin,
  2026-08-01):

  (a) OWN-CONCLUSION defect, NOT curable by dependency landing: the ↔'s
      right-hand side applies `MovesD.CanRealizes p F n f H` — the same
      application the III-T14m record above diagnoses.  The corpus predicate
      (`MovesD/R7_polFillReduction.lean:85`) takes ONE node ν plus ONE
      polynomial t with `p`,`F` implicit; exact compiler error at the
      displayed conclusion:
        `Application type mismatch: The argument p has type ℕ but is
         expected to have type MovesC.Node ?m.19 ?m.21 in the application
         MovesD.CanRealizes p`.

  (b) dependency defect: binder `(hab : M6ABHyps p F)` — `M6ABHyps` does not
      exist in the corpus (unit III-T14m, record above, is itself BLOCKED on
      the same row defect).  Exact error at the binder:
        `Function expected at M6ABHyps ... The identifier `M6ABHyps` is
         unknown`.

  (`MovesJ.ReadsOf p F n f H`, the ↔'s left-hand side, elaborates cleanly —
  probed; the defect is confined to the `CanRealizes` side.)

  Needs the SAME blueprint-level repair as III-T14m: how the history-level
  predicate "f can be realized along H" is assembled from the corpus one-node
  `CanRealizes` (which nodes of `H.nodes` carry a witness; where n enters) —
  fenced above this unit's authority.  Once repaired rows land, the intended
  proof shape on record: forward direction = the `m6a` row applied to the
  `ReadsOf` hypothesis; assembly = `Iff.intro` of that consumption with unit
  III-T14a's reverse direction (which consumes `m6b` + the `M6cHyps`/`GRB`
  row and is recorded separately by that unit).

```
theorem realEquiv_of_m6 {n : ℕ} {f : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hab : M6ABHyps p F) (hc : M6cHyps p F)
    (hcoh : MovesC.HistoryCoherent H) :
    MovesJ.ReadsOf p F n f H ↔ MovesD.CanRealizes p F n f H
```
-/

/-! ## Unit III-T14a — `realEquiv_of_m6` REVERSE direction (⟸): BLOCKED on the
same own-conclusion statement defect; independently, its content deps are not
landed

Unit III-T14a owns the ⟸ direction of the BP_III §1.7 `realEquiv_of_m6`
display (preserved verbatim in the III-T14b record above and again at the end
of this block), consuming the displayed `M6ABHyps` and `M6cHyps` rows.  It is
NOT weakened or partially landed (restating the ⟸ direction over any
substitute history-level predicate would be a statement change).  Status at
hand-off (2026-08-01):

* -- BLOCKED(III-T14a), NOT curable by dependency landing: the ⟸ direction's
  hypothesis side is the ↔'s right-hand side, `MovesD.CanRealizes p F n f H` —
  the identical per-node-arity defect diagnosed in the III-T14m record above.
  Exact compiler error, measured by this unit by transcribing the full
  verbatim theorem into a scratch module against this pin (Lean 4.31,
  2026-08-01):
    `Application type mismatch: The argument p has type ℕ but is expected to
     have type MovesC.Node ?m.19 ?m.21 in the application
     MovesD.CanRealizes p`
  at the displayed conclusion, plus the dep-curable
    `Function expected at M6ABHyps but this term has type ?m.1` (unknown
    identifier — III-T14m's `M6ABHyps` is itself BLOCKED, record above)
  at the `(hab : M6ABHyps p F)` binder.  (`MovesJ.ReadsOf p F n f H`
  elaborates cleanly — the compiled anchors below display both corpus
  signatures; the defect is confined to the `CanRealizes` side.)

* Content-dependency census for the ⟸ proof (independent second ground):
  III-H1 `GRB` LANDED (`Hyps.lean`), consumed here only through the landed
  `M6cHyps` row above; III-T11b BLOCKED (record above — elided display);
  III-T12 (`m6c_noPhantom`) NOT landed anywhere under `Scaffold/` at hand-off,
  its §1.7 display being likewise the ellipsis `theorem m6c_noPhantom …`.  The
  source proof on record (O1thr §2.5 Lemma REAL≡ (⟸), rev-4 requantified) is
  a prefix-by-prefix walk induction along `H.nodes` whose per-step
  non-halting cite is exactly (M6c)(ii) = III-T12 (with (M6c)(i) = III-T11
  beyond-window support and the `m6b` row supplying non-emptiness), so even
  after the arity ruling repairs the statement, the ⟸ body has no landed
  III-T11b/III-T12 statements to consume.

Needs the SAME architect ruling as III-T14m/III-T14b: a typed history-level
realizability predicate of arity (p F n f H) assembled from the one-node
corpus `CanRealizes` (e.g. quantified over `H`'s recentering nodes in the
style of `MovesD.RunRealizerExists`; the f-free `MovesD.Realizable` of
`TreeCan.lean` is NOT that predicate), then typed III-T11b/III-T12 statements.
The blocked display this unit owns the ⟸ direction of, for the record
(BP_III §1.7, verbatim):

```
theorem realEquiv_of_m6 {n : ℕ} {f : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hab : M6ABHyps p F) (hc : M6cHyps p F)
    (hcoh : MovesC.HistoryCoherent H) :
    MovesJ.ReadsOf p F n f H ↔ MovesD.CanRealizes p F n f H
```
-/

/-! Compiled anchors for the III-T14m/T14a/T14b records: the two corpus
signatures the §1.7 displays have to reconcile — `ReadsOf` takes (p F n f H)
explicitly; `CanRealizes` is per-node (ν t) with `p`,`F` implicit.  The arity
mismatch is visible right here. -/

#check @LeanUrat.MovesJ.ReadsOf
#check @LeanUrat.MovesD.CanRealizes

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-T15 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.vtx_htUpper_div
