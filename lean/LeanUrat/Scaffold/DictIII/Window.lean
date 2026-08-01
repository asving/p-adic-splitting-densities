/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.Scaffold.DictIII.Devid
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

/-! ## Unit III-T11a — (M6c)(i) degree-one statement, EXPLICITLY assuming `e′ = 1`
(BP_III §2 Wave 3 row T11a; sketch §1.7 `m6c_beyondWindow`; src O1thr §2.5 (M6c)(i))

STATEMENT-PROVENANCE RECORD (the honest part — read before consuming):

* BP_III §1.7 (line 524) displays this unit's theorem only as the ellipsis
  `theorem m6c_beyondWindow …` — there is NO verbatim blueprint statement to
  transcribe (same finding as the III-T11b record above; REV2 finding 1 left
  §1.7's three theorem displays elided).
* Unlike III-T11b, however, the blueprint pins THIS unit's statement to the
  corpus byte-for-byte, by three displayed constraints: the unit row (BP_III
  line 790: proof = corpus `UE.vtx_m6bi_n4upper` + `readBox_e1`, "no broader
  re-keying claim"), the §3.1 corpus-reuse map (line 859: "the e′ = 1
  perimeter + carried trio (hσL/hsteep/species) transfer as the units'
  DISPLAYED HYPOTHESES"), and the D-R4 fence (line 972: "III-T11a states only
  the `e′ = 1` corpus perimeter").  So the unit is landed in the III-T15
  re-export style: binders and conclusions transcribed character-for-character
  from the two named corpus theorems (`HC2/UE_vtxUpper.lean:108-125`,
  `HC2/HK11a_vertexTransport.lean:613-625`), source signatures typechecked by
  the `#check`s below, proof = the two exact applications.  NOT verbatim from
  the blueprint (nothing to be verbatim to); flagged for division-lead
  ratification as a statement, per the fence.
* Name: `m6c_beyondWindow_e1` — the bare sketch name `m6c_beyondWindow` is
  left to unit III-T11b's general GRB/OL2min theorem (D-R4: the degree-one
  result must not squat the general claim's name).
* SCOPE (what is and is NOT claimed): at a coherent `ReadsOf` record with a
  non-recentering read `i` (carried trio: tower provenance `hσL`, STRICT read
  steepness, species) and the EXPLICIT `e′ = 1` hypothesis on the child node,
  for f's development `B` in the recorded child key: (a) vertex support
  `B μ ≠ 0` ((M6b)(i)); (b) at every nonzero slot STRICTLY below the window
  vertex `μ`, the point lies STRICTLY above the recorded side line in the
  child frame's ℚ-scale (the (BOX) strictness — (R1)'s off-stride demand at
  the recorded window, `readBox_e1` byte-shape; the `e′`-stretch seam HK-52
  enters ONLY here, through `he'1`); (c)+(d) the (N4)-upper band at the
  vertex, slack and cleared forms (`vtx_m6bi_n4upper`, e′-unconditional).
  The `j > W` state-polygon flank of O1thr §2.5's (M6c)(i) prose is NOT among
  the row's named corpus suppliers and is NOT claimed here — per D-R4 it
  belongs to the general unit III-T11b (GRB/OL2min rows).  This also cures
  the III-T11b record's second blocking ground ("no landed anchor
  signature"): the `e′ = 1` anchor is now this declaration. -/

section UnitIIIT11a

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1
  LeanUrat.MovesJ

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

-- SOURCE signature displays + typecheck (III-T15's REV2-finding-26 gate, applied here).
#check @LeanUrat.MovesJ.UE.vtx_m6bi_n4upper
#check @LeanUrat.MovesJ.HK11a.readBox_e1

/-- **Unit III-T11a — the (M6c)(i) degree-one/`e′ = 1` corpus perimeter** (O1thr
§2.5 (M6c)(i); the beyond-window-support package at the recorded read).  See the
STATEMENT-PROVENANCE RECORD in the section header: statement = the two named
corpus theorems' conclusions at their shared binders (character-for-character);
proof = exactly their applications; no broader re-keying claim (D-R4).

Conclusions, in order: (a) `B μ ≠ 0` — (M6b)(i) vertex support; (b) the strict
(BOX) band — every nonzero slot strictly below the window vertex lies STRICTLY
above the recorded side line (child-frame ℚ-scale; the ONLY clause consuming
`he'1`); (c) the (N4)-upper with displayed shear slack; (d) its cleared form. -/
theorem m6c_beyondWindow_e1 {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (he'1 : (H.nodes[i+1]'hi1).e = 1)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
    (∀ j : ℕ, j < (H.nodes[i]'(by omega)).μ → B j ≠ 0 →
      (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
        < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ))) ∧
    ((H.nodes[i]'(by omega)).e : ℤ)
        * (H.nodes[i]'(by omega)).σ.w (B ((H.nodes[i]'(by omega)).μ))
      ≤ (H.nodes[i]'(by omega)).gam
        - ((H.nodes[i]'(by omega)).μ : ℤ)
          * (((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).h : ℤ)
            * ((H.nodes[i]'(by omega)).g : ℤ)) ∧
    ((H.nodes[i]'(by omega)).e : ℤ)
        * (H.nodes[i]'(by omega)).σ.w (B ((H.nodes[i]'(by omega)).μ))
      ≤ (H.nodes[i]'(by omega)).gam := by
  obtain ⟨hBμne, hslack, hclear⟩ :=
    UE.vtx_m6bi_n4upper h i hi1 hsp hσL hsteep B Nd hdev
  refine ⟨hBμne, ?_, hslack, hclear⟩
  intro j hjμ hjne
  exact HK11a.readBox_e1 h i hi1 hsp hσL hsteep he'1 B Nd hdev j hjμ hjne

end UnitIIIT11a

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

* RE-VERIFIED by unit III-T14b's own execution pass (2026-08-01, fresh
  transcription of the verbatim display against this pin): both errors
  reproduce character-for-character — the `CanRealizes` arity mismatch at
  the ↔'s RHS and the unknown-identifier `M6ABHyps` at the `hab` binder;
  the ReadsOf LHS elaborates cleanly.  Updated dependency census at this
  pass: III-H1 `GRB` LANDED (`Hyps.lean`, consumed via `M6cHyps` below);
  III-T12 `m6c_noPhantom` NOW LANDED in this file (all legs proved except
  the window-confinement leg's honest sorry, record at that unit); III-T11b
  still BLOCKED (elided display, record above); III-T14m's `M6ABHyps` still
  BLOCKED (row defect, record above); III-T14a BLOCKED (record below).
  None of this cures ground (a): the defect is in this unit's OWN displayed
  conclusion, so the verdict stands independent of dependency landings.

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

* RE-VERIFIED by unit III-T14a's own execution pass (2026-08-01, fresh
  scratch transcription of the verbatim `M6ABHyps` rows + `realEquiv_of_m6`
  display against this pin, per the trust boundary — comments are not ground
  truth): the identical `Application type mismatch … MovesC.Node ?m.18 ?m.20
  … MovesD.CanRealizes p` fires AT THE THEOREM'S OWN CONCLUSION (the ⟸
  hypothesis side) even with the M6ABHyps rows present in scope, confirming
  the defect is own-statement, not dependency-shaped.

* Content-dependency census for the ⟸ proof (independent second ground;
  REFRESHED at the 2026-08-01 re-measurement pass, which found the earlier
  census stale on the III-T12 line): III-H1 `GRB` LANDED (`Hyps.lean`),
  consumed here only through the landed `M6cHyps` row above; III-T11b still
  BLOCKED (record above — elided display); III-T12 (`m6c_noPhantom`) now
  LANDED BELOW IN THIS FILE (section `UnitIIIT12` — statement completed under
  its delegated-statement charter, everything proved EXCEPT the window-
  confinement leg, which carries an honest sorry pending III-T11b/III-T13).
  The source proof on record (O1thr §2.5 Lemma REAL≡ (⟸), rev-4
  requantified) is a prefix-by-prefix walk induction along `H.nodes` whose
  per-step non-halting cite is exactly (M6c)(ii) = III-T12 (with (M6c)(i) =
  III-T11 beyond-window support and the `m6b` row supplying non-emptiness).
  So the ⟸ body's per-step supplier is now partially in place, but the walk
  still has no landed III-T11b statement to consume and III-T12's
  confinement leg is itself conditional — and none of this reaches the
  PRIMARY ground: the ⟸ direction's OWN hypothesis side does not elaborate.

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

/-! ## Unit III-T12 — `m6c_noPhantom` ((M6c)(ii) no-phantom; BP_III §2 Wave 3
row T12, pre-split T12a stmt / T12b proof; src O1thr rev 4 §2.5 (M6c)(ii))

STATEMENT-PROVENANCE RECORD (the III-T11a convention — read before consuming):

* BP_III §1.7 (line 529) displays this unit's theorem only as the ellipsis
  `theorem m6c_noPhantom …` — there is NO verbatim blueprint statement to
  transcribe (REV2 finding 1 left §1.7's three theorem displays elided; the
  same finding as the III-T11a/T11b records above).  UNLIKE III-T11b,
  statement composition is IN this unit's charter: the BP pre-splits III-T12
  into "T12a stmt (EASY) / T12b proof" (unit row 792) — a DELEGATED statement
  unit in the III-G21a sense (see `Devid.lean`'s III-G21b record, which
  contrasts exactly these two situations).  So the statement below is
  COMPLETED from the source of record per the DictIII convention
  (`Devid.lean` unit III-G18), source sentence O-1thr rev 4 §2.5 (M6c)(ii)
  (`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md` lines 552–559 and
  the Proof-of-(M6c) display, lines 781–809).  Flagged for division-lead
  ratification as a statement, per the fence.

COMPLETION LEDGER (source clause → corpus rendering):

* Site: BP §1.6's convention — "the site is a corpus `History` prefix + next
  node".  The state o = `H : History p F`; the child ν′ = a non-root `Node`;
  the chain o·ν′ = `H.snoc ν' hν'`.  Corpus histories are NONEMPTY, so this
  site is the NON-ROOT-STATE leg of the source quantifier (o's creating read
  = `H.nodes.getLast`); the source's root-state instances (child = the root
  read itself, not expressible as a `snoc`) belong to Lemma ROOT-M's unit
  III-T16 and are NOT claimed here.
* READ(f, o·ν′) = `ReadsOf p F n f (H.snoc ν' hν')` — the rev-4 WEAKENED
  child hypothesis, verbatim: NO halting hypothesis, NO `Realizable`, NO
  LAWFUL/AUX enter (the rev-4 requantification; ¬NsHalts is a CONCLUSION).
* (N1) (`pat(0) ≠ 0`, `pat(wSide/e) ≠ 0`) is INTRINSIC to the corpus child —
  `Node.hpat0`/`Node.hpatTop`; no separate hypothesis is displayed.
* "arises from a (window principal face, ψ′) pair, records equal to that
  pair's harvest": the face is exhibited on f's development in the STATE key
  `ν'.σ.Φ` (`HistoryCoherent` inside `ReadsOf` ties `ν'.σ` to o's frame).
  `SideReads ν' B Nd Φnext` carries the record-vs-f harvest ties verbatim —
  (i) the side line supports ALL slots with equality ONLY at recorded strides
  ((R1)), (ii) the stride digits ARE pat′ ((R2)), (iii) the anchored residual
  + `ord_ψ` read ((R3)), (iv) landing on the produced key ((R4)), (vi) the
  vertex pair ((R5)).  The two displayed ENDPOINT clauses are the
  (N1)-driven reconstruction step ("by (R2) + (N1) BOTH endpoints are
  touched"): the support segment is a genuine FACE — occupied at both ends
  at the exact side value γ′ — not merely a supporting line.
* ψ′ leg ("ψ′ is a monic irreducible with ord_{ψ′}(R_F) = μ′ ≥ 1"):
  `Irreducible ν'.ψ ∧ OrdPsiPoly ν'.ψ ν'.Ranch ν'.μ ∧ 1 ≤ ν'.μ` (monicity is
  the record's `Node.hψmonic`).
* ¬NsHalts(o, f) as a CONCLUSION: the corpus (τ-ns) face is "the window
  admits no side" (`MovesT/Defs.lean` (τ-ns) docstring: J(f) = ∅); its
  negation IS the displayed existential — o's window admits the principal
  side (F, ψ′) (principality −h′/e′ < 0 from `Node.he`/`Node.hh`).  The
  `MovesT.TreeModel`-keyed corollary is the T14/CU-1 consumers' one-liner
  once a concrete `T.child` ties children to `ReadsOf`; no `TreeModel`
  enters §1.7's vocabulary.
* Window confinement F ⊆ [0, W_o] (W_o = the creating read's μ — source
  §2.5 preamble "(e, h, γ, ψ, μ = W) the creating read ν's data"): the final
  clause, keyed to `H.nodes.getLast?`.  This is the source proof's ONE
  citation of (M6c)(i)-at-o / WGEO(c) ("F is principal, and F ⊆ [0, W]"),
  and it is exactly the `j > W` state-polygon flank that the III-T11a record
  above declares NOT claimed at `e′ = 1` and D-R4 assigns to III-T11b —
  BLOCKED (record above).  The clause is stated in full and carries an
  honest `sorry` (BLOCKED(III-T12) note at the leg); the
  `IsPolyValuation`/`KeyPkg` rows it will consume are bound in the signature
  per the unit charter ("under KeyPkg rows"): `wS` abstracts the state
  valuation w_o, `hwS` its frame tie (a NAMED row, the III-G18 convention),
  `hval` = (V1) at the state (`Devid.lean`'s un-indexed `MacLaneV1Pkg` row
  set), `hkp` = (V2)-front at the state key (III-H8's landed structure).
  Row SUFFICIENCY for this leg is III-T13 (`wgeo`) territory and
  unadjudicated; if `wgeo` lands with a different row set, this signature is
  a re-adjudication item, not a silent edit.

Everything EXCEPT the confinement leg is PROVED below from the run record
alone (snoc index bookkeeping + the (N1) endpoint consumption + the `hEdvd`
stride arithmetic); no axiom, no new carrier, no `Node`/`SideReads` field
redeclared. -/

section UnitIIIT12

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesJ

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- III-T12 support (run-record extraction): `ReadsOf` at a snoc-extended
chain yields the LAST read's development/side witnesses at the appended node —
the index bookkeeping `(H.snoc ν' hν').nodes[H.nodes.length] = ν'` done
once. -/
theorem lastRead_of_readsOf_snoc {n : ℕ} {f : Polynomial ℤ_[p]}
    {H : History p F} (ν' : Node p F)
    (hν' : ν'.species ≠ ReadSpecies.root)
    (hread : ReadsOf p F n f (H.snoc ν' hν')) :
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
      IsDevelopment ν'.σ.Φ f B Nd ∧ SideReads ν' B Nd Φnext := by
  obtain ⟨_, _, _, hrun⟩ := hread
  have hi : H.nodes.length < (H.snoc ν' hν').nodes.length := by
    change H.nodes.length < (H.nodes ++ [ν']).length
    simp
  obtain ⟨B, Nd, Φnext, hdev, _, hside⟩ := hrun H.nodes.length hi
  have hlast : (H.snoc ν' hν').nodes[H.nodes.length]'hi = ν' := by
    change (H.nodes ++ [ν'])[H.nodes.length]'hi = ν'
    simp
  rw [hlast] at hdev hside
  exact ⟨B, Nd, Φnext, hdev, hside⟩

/-- **Unit III-T12 (`m6c_noPhantom` — O-1thr rev 4 §2.5 (M6c)(ii), BP_III
§1.7): no phantom, at the corpus non-root site.**  Every child `ν'` at the
state `H` whose extended chain satisfies READ(f, H·ν′) — the rev-4 WEAKENED
child hypothesis; (N1) is the child's own `hpat0`/`hpatTop`; NO halting
hypothesis enters — arises from a (window principal face, ψ′) harvest pair:
f's development in the STATE key `ν'.σ.Φ` admits the recorded side as a
genuine face (support + stride-exact equality via `SideReads`, BOTH endpoints
occupied at the exact side value γ′), with records equal to that pair's
harvest (`SideReads` (i)–(vi)) and `ψ′ = ν'.ψ` a monic irreducible with
`ord_{ψ′}(R_F) = μ′ ≥ 1`.  IN PARTICULAR o's window admits a principal side —
the corpus (τ-ns) face of ¬NsHalts(o, f) is exactly this CONCLUSION.  The
final clause is the window confinement F ⊆ [0, W_o] (W_o = the creating
read's `μ`), the (M6c)(i)/WGEO(c) leg carried on the
`IsPolyValuation`/`KeyPkg` rows — see the section header's ledger and the
BLOCKED note at the leg. -/
theorem m6c_noPhantom {n : ℕ} {f : Polynomial ℤ_[p]}
    {H : History p F} (ν' : Node p F)
    (hν' : ν'.species ≠ ReadSpecies.root)
    (wS : Polynomial ℤ_[p] → WithTop ℤ)
    (hval : IsPolyValuation wS)
    (hkp : KeyPkg wS ν'.σ.Φ)
    (hwS : ∀ B : Polynomial ℤ_[p], B ≠ 0 → wS B = ((ν'.σ.w B : ℤ) : WithTop ℤ))
    (hread : ReadsOf p F n f (H.snoc ν' hν')) :
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
      -- the harvest pair's face, on f's development in the STATE key:
      IsDevelopment ν'.σ.Φ f B Nd ∧
      -- records = the pair's harvest (support/strides/digits/residual/
      -- landing/vertex — SideReads (i)–(vi) verbatim):
      SideReads ν' B Nd Φnext ∧
      -- (N1)-reconstruction, LEFT endpoint occupied at exact height γ′:
      (B ν'.s0 ≠ 0 ∧
        (ν'.e : ℤ) * ν'.σ.w (B ν'.s0) + (ν'.s0 : ℤ) * (ν'.h : ℤ) = ν'.gam) ∧
      -- (N1)-reconstruction, RIGHT endpoint occupied at exact height γ′:
      (B (ν'.s0 + ν'.wSide) ≠ 0 ∧
        (ν'.e : ℤ) * ν'.σ.w (B (ν'.s0 + ν'.wSide))
          + ((ν'.s0 + ν'.wSide : ℕ) : ℤ) * (ν'.h : ℤ) = ν'.gam) ∧
      -- the ψ′ harvest coordinate: irreducible, ord_{ψ′}(R_F) = μ′ ≥ 1
      -- (monicity is the record's `hψmonic`):
      (Irreducible ν'.ψ ∧ OrdPsiPoly ν'.ψ ν'.Ranch ν'.μ ∧ 1 ≤ ν'.μ) ∧
      -- window confinement F ⊆ [0, W_o], W_o = the creating read's μ:
      (∀ νW : Node p F, H.nodes.getLast? = some νW →
        ν'.s0 + ν'.wSide ≤ νW.μ) := by
  obtain ⟨B, Nd, Φnext, hdev, hside⟩ := lastRead_of_readsOf_snoc ν' hν' hread
  refine ⟨B, Nd, Φnext, hdev, hside, ?_, ?_, ⟨ν'.hψirr, ν'.hOrd, ν'.hμ⟩, ?_⟩
  · -- LEFT endpoint: SideReads (ii) DIGITS at k = 0, fired by (N1)'s `hpat0`
    have h0 := hside.2.1 0 (Nat.zero_le _) ν'.hpat0
    have he0 : ν'.s0 + ν'.e * 0 = ν'.s0 := by simp
    rw [he0] at h0
    exact ⟨h0.1, h0.2.1⟩
  · -- RIGHT endpoint: SideReads (ii) DIGITS at k = wSide/e, fired by (N1)'s
    -- `hpatTop`; `e ∣ wSide` (`hEdvd`) closes the stride arithmetic
    have htop := hside.2.1 (ν'.wSide / ν'.e) (le_refl _) ν'.hpatTop
    have heTop : ν'.s0 + ν'.e * (ν'.wSide / ν'.e) = ν'.s0 + ν'.wSide := by
      rw [Nat.mul_div_cancel' ν'.hEdvd]
    rw [heTop] at htop
    exact ⟨htop.1, htop.2.1⟩
  · -- window confinement F ⊆ [0, W_o]
    intro νW hW
    -- BLOCKED(III-T12): this leg is the source proof's ONE citation of
    -- (M6c)(i)-at-o / WGEO(c) ("F is principal, and F ⊆ [0, W]") — the
    -- `j > W` beyond-window strictness at the child's own line, from which
    -- confinement follows because the RIGHT endpoint is TOUCHED (clause
    -- above): a touched slot beyond W would violate strictness.  That
    -- strictness is exactly the state-polygon flank the III-T11a record
    -- above declares NOT claimed at `e′ = 1` and D-R4 assigns to III-T11b —
    -- BLOCKED (elided display; record above) — with III-T13 (`wgeo`) not
    -- landed and its dep III-G21 (`gd3_min`) BLOCKED per `Devid.lean`.
    -- The bound rows `wS`/`hval`/`hkp`/`hwS` are this leg's declared supply
    -- per the unit charter ("under KeyPkg rows"); the leg completes when
    -- III-T11b/III-T13 land.  Honest sorry — the statement is NOT weakened.
    sorry

end UnitIIIT12

/-! ## Unit III-T13 — `wgeo` over the named rows (BP_III §2 Wave 3 row T13;
src O1thr §2.5 WGEO; GD23 §4 Cor)

Blueprint display (BP_III §1.7, ELIDED after its opening binders — the same
REV2-finding-1 residue as the III-T11/T12 records above):

    /-- Lemma WGEO over the named key-compliance rows (V1) = MacLaneV1Pkg,
        (V2a) = KeyPkg.KPa, (V2b) = devid, (V2c) = gd3_min — the GD23 re-founding. -/
    theorem wgeo (hv1 : MacLaneV1Pkg …) (hkp : KeyPkg …) …

Statement completion is IN this unit's charter (the unit row pins the
consumption structure: "the four consumptions (V1)/(V2a)/(V2b)/(V2c) =
H8/G17/G21 exactly as GD23's re-founding displays"), so — same sanctioned
convention as Devid.lean's III-G18/G19/G20/G21a — the statement is completed
from the sources of record: O-1thr rev 4 §2.5 Lemma WGEO
(`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`, lines 678–745) and
GD23 rev 4 §4 Corollaries ("**WGEO re-founded.** O-1thr's Lemma WGEO consumes
(V1), (V2a) = (KPa), (V2b) = DEVID, (V2c) = GD3-MIN"), preserving every
displayed token (`wgeo`, `hv1 : MacLaneV1Pkg …`, `hkp : KeyPkg …`, the
docstring).  Flagged for division-lead ratification as a statement, per the
fence.

COMPLETION LEDGER (row-by-row provenance):

* Index dictionary: the state is level `i + 1` with state valuation `w (i+1)`
  and produced key `keys i` — EXACTLY `tie_w_eq_v`'s convention (Devid.lean
  III-G20: `hkeyW : w (i+1) (keys i) = γ i`, `hdevW : w (i+1) B =
  minDev (w (i+1)) (keys i) B`).  `γ` is the state value `w (i+1) f`;
  `u_k := w(C_k) + k·w(Φ)` the sheared heights of the development slots
  `C_k = devCoeff (keys i) f k`.
* `hv1` — **(V1)** = III-H8's `MacLaneV1Pkg`, verbatim, consumed through its
  level-(i+1) row set (= Devid.lean's `IsPolyValuation`, per that file's
  recorded dedupe note).
* `hkp` — **(V2a)** = III-H8's `KeyPkg` at the state pairing
  `(w (i+1), keys i)` (GD23 §4's DEVID convention: the key block travels with
  the state valuation whose development it controls).  Its `monic` and
  `positiveDegree` rows fire below; the weight-level `initialPrime`/
  `lowerDegreeBlock` rows are carried in the package while the graded work is
  done by the graded renderings next.
* `G`, `hkpa` — (V2a)'s graded rendering `KPaBlock` on the landed III-G15a
  carrier (`Devid.lean`'s recorded DEVID convention: "`KPaBlock` [is] §1.5's
  graded rendering of III-H8's `KeyPkg`"); `hkpa` is consumed by the
  `gd3_min` firing (its "under KeyPkg" binder).
* `hV2a` — (V2a)'s CONSUMED divisibility block, the O-1thr rev-4 bridge
  sentence (its G2 fix): "ψ̂_hom ∤ in(B) for every nonzero B of
  deg < deg Φ_{i+1} — the exact form (V2a) that WGEO(b) consumes", rendered
  through IMAGE divisibility exactly as III-G21a's `GrOrdAt` ledger renders
  ψ̂-orders (the `ValGr` interface carries no divisibility operation).
* `hloc`, `hsep` — **(V1)'s graded-piece laws**: the two working directions
  of III-G18's `hfaith` row ("equal-weight initial forms coincide iff the
  difference sits strictly higher" — GD23 §1.3 (g1)/(g3) via §5 BRIDGE),
  0-corner-guarded: `hloc` = higher-weight terms are invisible to the initial
  form; `hsep` = equal initial forms force strictly higher difference weight,
  at non-⊤ weight.  NAMED rows, never axioms.  They are NOT derivable from
  the landed `ValGr` rows and are LOAD-BEARING: the D-R3 identity probe
  (`valGrIdentity`) satisfies every `ValGr` row yet fails `hloc`, and under
  the identity carrier conclusion (b) below is FALSE — sketch countermodel,
  the SAME interface seam as III-G16's compiled refutation: for the
  (e,h) = (2,1) monomial valuation on ℤ₂[x] at Φ = X, f = X + 2, the dev
  slots have u₀ = w(2) = 2, u₁ = w(1) + w(X) = 1, so first attainment sits at
  slot 1, while the identity-carrier graded order of `in f` is the exact
  X-divisibility order 0.  So the graded-piece laws are exactly what the GD23
  re-founding prices into (V1), and they enter as displayed rows pending the
  queued III-G15a/G16 interface adjudication.
  RECORD (flag for review; G18 untouched): III-G18's `hfaith` row is stated
  unguarded and is unsatisfiable at `A = B = 0` (`inF 0 = inF 0` holds by
  `rfl` while `w 0 < w (0 - 0)` is `⊤ < ⊤`); the guarded split used here
  avoids that corner.
* `hdev` — **(V2b) = `devid`**: the assembled DEVID conclusion as a NAMED
  row, in `hdevW`'s exact shape (III-G20).  III-G17 is UNLANDED — its ≤ half
  III-G16 is REFUTED over the landed interface (Devid.lean's compiled
  countermodel) — so the identity is consumed as a hypothesis row, which is
  precisely how the GD23 re-founding DISPLAYS the consumption
  ("(V2b) = DEVID"); when the adjudicated `devid` lands, this row is its
  exact conclusion and consumers discharge it by one application.
* `ψ`, `Rlam`, `A`, `hres` — **(V2c) = `gd3_min`**: the level's anchored
  residual read (`AnchoredRead`, III-G21a's landed row package) and the
  residual ψ-order `μ = ord_ψ(R_λ f)`, FIRED through the PROVED III-G21a
  theorem `gd3_min` inside the proof.  `A.cancel`/`A.key_ne` also supply the
  graded cancellation of the source proof's rev-4 G3′ repair ("only
  non-divisibility and domain cancellation, no primeness, no unit status").
* `htop` — the state value of `f` is finite: the source's standing "f ≠ 0
  read at a genuine valuation", not derivable from the H8 rows over the total
  `WithTop ℤ` carrier (same convention as III-G19's `hzero` row).

SCOPE (the unit's honest perimeter): the conclusion is the WGEO **(a)/(b)**
display — the graded core at which all four consumptions fire:

* (a) `u_k ≥ γ` at every slot with `C_k ≠ 0`;
* (b) `u_μ = γ` (in particular `C_μ ≠ 0`) and `u_k > γ` for every `k < μ` —
  FIRST attainment at exactly `μ`, the rev-4 flag ("u_k = γ at slots k > μ is
  neither excluded nor needed; (c)/(d) consume only first attainment").

Clauses (c)/(d) of the source display (window-hull faces strictly descend;
principal part of the full polygon = window hull; beyond-window points
strictly above every window face's extended line) are convexity
re-expressions of (a)/(b) in the Newton-polygon/hull vocabulary owned by unit
III-A6's carrier (unlanded) — NOT claimed here; recorded as delegated.  The
III-T12 confinement leg above consumes exactly the (b)+(a) core once its
site's rows are instantiated — that wiring is III-T12's re-adjudication item,
not silently performed here. -/

section UnitIIIT13

open Polynomial

-- (Slot-vanishing of the zero polynomial: `devCoeff_zero_poly`, shared with
-- the III-G23 wave, is consumed from `Devid.lean` — the dedup rule.)

-- WAVE-QUARANTINE(BP_II Wave 3g checkpoint, dedup): the III-T13 support copy
-- of `devCoeff_eq_zero_of_natDegree_lt` below duplicated the SAME name in the
-- SAME namespace as GDOrder1.lean's (unit III-G1 wave) — a duplicate-constant
-- import error once Devid.lean deduped its `devCoeff` against GDOrder1 (this
-- file now transitively imports GDOrder1).  GDOrder1's form is strictly
-- stronger (no `[Nontrivial K]` assumption; same explicit-argument order), so
-- the use site below (`wgeo_kernel`) consumes it unchanged.  Full decl
-- preserved:
-- /-- III-T13 support: development slots beyond the degree vanish (monic key of
-- positive degree) — the slot-support fact that lets WGEO(a) quantify over ALL
-- slots under the displayed `C_k ≠ 0` guard. -/
-- theorem devCoeff_eq_zero_of_natDegree_lt {K : Type*} [CommRing K]
--     [Nontrivial K] {Φ : Polynomial K} (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) :
--     ∀ (k : ℕ) (B : Polynomial K), B.natDegree < k → devCoeff Φ B k = 0 := by
--   intro k
--   induction k with
--   | zero => intro B hB; omega
--   | succ k ih =>
--     intro B hB
--     simp only [devCoeff]
--     by_cases hq : B /ₘ Φ = 0
--     · rw [hq]; exact devCoeff_zero_poly Φ k
--     · refine ih _ ?_
--       have h1 : ¬ B.degree < Φ.degree := fun h =>
--         hq ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr h)
--       have h2 : Φ.natDegree ≤ B.natDegree :=
--         Polynomial.natDegree_le_natDegree (not_lt.mp h1)
--       rw [Polynomial.natDegree_divByMonic B hΦ]
--       omega

/-- III-T13 support — the WGEO(a)/(b) kernel at a bare state `(W, Φ)`: the
    theorem `wgeo` below is exactly this kernel fired at the indexed state
    `(w (i+1), keys i)` with the (V1)/(V2a) packages unbundled into the rows
    consumed here (`IsPolyValuation` = `MacLaneV1Pkg`'s level row set;
    `monic`/`positiveDegree` = `KeyPkg`'s fired rows).  Kept separate so the
    slot bookkeeping runs over honest free variables; the row provenance is
    the section header's ledger. -/
theorem wgeo_core {K : Type*} [CommRing K] [Nontrivial K]
    (W : Polynomial K → WithTop ℤ) (hval : IsPolyValuation W)
    (Φ : Polynomial K) (hmon : Φ.Monic) (hdeg : 1 ≤ Φ.natDegree)
    (G : ValGr W) (hkpa : KPaBlock W G Φ)
    (hV2a : ∀ B : Polynomial K, B ≠ 0 → B.natDegree < Φ.natDegree →
      ¬ ∃ C : Polynomial K, G.inF B = G.inF (Φ * C))
    (hloc : ∀ X Y : Polynomial K, W X < W Y → G.inF (X + Y) = G.inF X)
    (hsep : ∀ X Y : Polynomial K, W X ≠ ⊤ →
      G.inF X = G.inF Y → W X < W (X - Y))
    (hdev : ∀ B : Polynomial K, B ≠ 0 → W B = minDev W Φ B)
    {𝒦 : Type*} [Field 𝒦] (ψ : Polynomial 𝒦)
    (Rlam : Polynomial K → Polynomial 𝒦)
    (A : AnchoredRead G Φ ψ Rlam)
    (f : Polynomial K) (hf : f ≠ 0) (htop : W f ≠ ⊤)
    (μ : ℕ) (hres : Moves.OrdPsiPoly ψ (Rlam f) μ) :
    (∀ k, devCoeff Φ f k ≠ 0 → W f ≤ W (devCoeff Φ f k) + k • W Φ) ∧
    W (devCoeff Φ f μ) + μ • W Φ = W f ∧
    (∀ k, k < μ → W f < W (devCoeff Φ f k) + k • W Φ) ∧
    devCoeff Φ f μ ≠ 0 := by
  classical
  have hrne : (Finset.range (f.natDegree + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  -- (V2b) fires: γ is the slot inf'
  have hγ : W f = Finset.inf' (Finset.range (f.natDegree + 1)) hrne
      (fun k => W (devCoeff Φ f k) + k • W Φ) := by
    rw [hdev f hf]; rfl
  -- (a) on the recorded slot range
  have ha : ∀ k ∈ Finset.range (f.natDegree + 1),
      W f ≤ W (devCoeff Φ f k) + k • W Φ := by
    intro k hk
    rw [hγ]
    exact Finset.inf'_le _ hk
  -- (a) at every slot, under the displayed `C_k ≠ 0` guard
  have hA : ∀ k, devCoeff Φ f k ≠ 0 →
      W f ≤ W (devCoeff Φ f k) + k • W Φ := by
    intro k hk
    by_cases hkr : k ∈ Finset.range (f.natDegree + 1)
    · exact ha k hkr
    · refine absurd (devCoeff_eq_zero_of_natDegree_lt hmon hdeg k f ?_) hk
      have hkr' : ¬ k < f.natDegree + 1 := fun h => hkr (Finset.mem_range.mpr h)
      omega
  -- the attainment set S₀ and its FIRST slot m
  set S := (Finset.range (f.natDegree + 1)).filter
    (fun k => W (devCoeff Φ f k) + k • W Φ = W f) with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨k, hk, hke⟩ := Finset.exists_mem_eq_inf' hrne
      (fun k => W (devCoeff Φ f k) + k • W Φ)
    refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩⟩
    have hke' := hke.symm
    rw [← hγ] at hke'
    exact hke'
  set m := S.min' hSne with hmdef
  have hmS : m ∈ S := Finset.min'_mem S hSne
  have hmrange : m ∈ Finset.range (f.natDegree + 1) :=
    (Finset.mem_filter.mp hmS).1
  have hum : W (devCoeff Φ f m) + m • W Φ = W f := (Finset.mem_filter.mp hmS).2
  have hmle : ∀ k ∈ S, m ≤ k := fun k hk => Finset.min'_le S k hk
  -- the vertex slot is inhabited, with finite value pieces
  have hCm0 : devCoeff Φ f m ≠ 0 := by
    intro h0
    apply htop
    rw [← hum, h0, hval.zero, top_add]
  have hmWΦ : m • W Φ ≠ ⊤ := by
    intro h
    apply htop
    rw [← hum, h, add_top]
  -- the min-weight part T and the strictly heavy tail R
  set T := ∑ k ∈ S, devCoeff Φ f k * Φ ^ k with hTdef
  set R := ∑ k ∈ (Finset.range (f.natDegree + 1)).filter
      (fun k => ¬ (W (devCoeff Φ f k) + k • W Φ = W f)),
      devCoeff Φ f k * Φ ^ k with hRdef
  have hTR : T + R = f := by
    rw [hTdef, hRdef, hSdef, Finset.sum_filter_add_sum_filter_not]
    exact devCoeff_sum Φ hmon hdeg f
  have hterm : ∀ k, W (devCoeff Φ f k * Φ ^ k)
      = W (devCoeff Φ f k) + k • W Φ := by
    intro k
    rw [hval.mul, hval.w_pow]
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp htop
  have hRgt : W f < W R := by
    have hstep : ∀ k ∈ (Finset.range (f.natDegree + 1)).filter
        (fun k => ¬ (W (devCoeff Φ f k) + k • W Φ = W f)),
        ((g + 1 : ℤ) : WithTop ℤ) ≤ W (devCoeff Φ f k * Φ ^ k) := by
      intro k hk
      obtain ⟨hkr, hkne⟩ := Finset.mem_filter.mp hk
      have h3 : W f < W (devCoeff Φ f k) + k • W Φ :=
        lt_of_le_of_ne (ha k hkr) (fun h => hkne h.symm)
      rw [hterm k]
      rcases eq_or_ne (W (devCoeff Φ f k) + k • W Φ) ⊤ with htk | htk
      · rw [htk]; exact le_top
      · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp htk
        rw [← hv]
        rw [← hg, ← hv] at h3
        have hgv : g < v := by exact_mod_cast h3
        exact_mod_cast Int.add_one_le_iff.mpr hgv
    calc W f = ((g : ℤ) : WithTop ℤ) := hg.symm
      _ < ((g + 1 : ℤ) : WithTop ℤ) := by exact_mod_cast lt_add_one g
      _ ≤ W R := by rw [hRdef]; exact hval.le_w_sum _ _ _ hstep
  -- the min-weight part carries the state value
  have hTγ : W T = W f := by
    refine le_antisymm ?_ ?_
    · by_contra hlt
      push_neg at hlt
      have h1 := hval.add T R
      rw [hTR] at h1
      exact absurd ((lt_min hlt hRgt).trans_le h1) (lt_irrefl _)
    · have h1 := hval.add f (-R)
      have e1 : f + -R = T := by rw [← hTR]; ring
      rw [e1, hval.w_neg] at h1
      exact le_trans (le_min le_rfl (le_of_lt hRgt)) h1
  -- (V1)'s locality row fires: in f = in T
  have hfT : G.inF f = G.inF T := by
    rw [← hTR]
    exact hloc T R (by rw [hTγ]; exact hRgt)
  -- factor the key power out of the min-weight part
  set B₀ := ∑ k ∈ S, devCoeff Φ f k * Φ ^ (k - m) with hB₀def
  have hTB₀ : T = Φ ^ m * B₀ := by
    rw [hTdef, hB₀def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmk : m ≤ k := hmle k hk
    have h5 : Φ ^ k = Φ ^ m * Φ ^ (k - m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h5]; ring
  have hfB₀ : G.inF f = G.inF (Φ ^ m * B₀) := by rw [hfT, hTB₀]
  have hWB₀ : W B₀ ≠ ⊤ := by
    intro h
    apply htop
    have h1 : W (Φ ^ m * B₀) = W f := by rw [← hTB₀]; exact hTγ
    rw [hval.mul, h, add_top] at h1
    exact h1.symm
  -- the graded order of in f at the key IS the first attainment slot m
  have hgrm : GrOrdAt G Φ f m := by
    refine ⟨⟨B₀, hfB₀⟩, ?_⟩
    rintro ⟨B, hB⟩
    -- cancel the key power ((V2c)'s cancellation rows; the rev-4 G3′ shape)
    have h1 : G.inF (Φ ^ m * B₀) = G.inF (Φ ^ m * (Φ * B)) := by
      rw [← hfB₀, hB]
      exact congrArg G.inF (by ring)
    rw [G.g2, G.g2] at h1
    have h2 : G.inF B₀ = G.inF (Φ * B) :=
      A.cancel _ _ _ (G.inF_pow_ne A.key_ne m) h1
    -- peel the vertex slot off B₀
    set E := ∑ k ∈ S.erase m, devCoeff Φ f k * Φ ^ (k - m - 1) with hEdef
    have hΦEsum : Φ * E = ∑ k ∈ S.erase m, devCoeff Φ f k * Φ ^ (k - m) := by
      rw [hEdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hmk : m ≤ k := hmle k (Finset.mem_of_mem_erase hk)
      have hkm : k ≠ m := Finset.ne_of_mem_erase hk
      have h5 : Φ ^ (k - m) = Φ * Φ ^ (k - m - 1) := by
        conv_lhs => rw [show k - m = (k - m - 1) + 1 by omega]
        rw [pow_succ]
        ring
      rw [h5]; ring
    have hB₀E : B₀ = devCoeff Φ f m + Φ * E := by
      have h6 := Finset.add_sum_erase S
        (fun k => devCoeff Φ f k * Φ ^ (k - m)) hmS
      rw [hB₀def, ← h6, Nat.sub_self, pow_zero, mul_one, hΦEsum]
    -- every erased attaining slot sits exactly at the vertex weight
    have hΦE : W (devCoeff Φ f m) ≤ W (Φ * E) := by
      rw [hΦEsum]
      refine hval.le_w_sum _ _ _ fun k hk => ?_
      have hkS := Finset.mem_of_mem_erase hk
      have hmk : m ≤ k := hmle k hkS
      have huk : W (devCoeff Φ f k) + k • W Φ = W f :=
        (Finset.mem_filter.mp hkS).2
      have h7 : (W (devCoeff Φ f k) + (k - m) • W Φ) + m • W Φ
          = W (devCoeff Φ f m) + m • W Φ := by
        rw [add_assoc, ← add_nsmul, show k - m + m = k from by omega, huk]
        exact hum.symm
      have h8 : W (devCoeff Φ f k) + (k - m) • W Φ = W (devCoeff Φ f m) :=
        WithTop.add_right_cancel hmWΦ h7
      rw [hval.mul, hval.w_pow, h8]
    -- (V1)'s separation row fires at the cancelled equation
    have hsep' : W B₀ < W (B₀ - Φ * B) := hsep B₀ (Φ * B) hWB₀ h2
    have hδB₀ : W (devCoeff Φ f m) ≤ W B₀ := by
      rw [hB₀E]
      exact le_trans (le_min le_rfl hΦE) (hval.add _ _)
    have e2 : devCoeff Φ f m = Φ * (B - E) + (B₀ - Φ * B) := by
      rw [hB₀E]; ring
    have hkey : W (Φ * (B - E)) < W (B₀ - Φ * B) := by
      by_contra hcon
      push_neg at hcon
      have h10 : W (B₀ - Φ * B) ≤ W (devCoeff Φ f m) := by
        rw [e2]
        exact le_trans (le_min hcon le_rfl) (hval.add _ _)
      exact absurd (lt_of_le_of_lt (h10.trans hδB₀) hsep') (lt_irrefl _)
    have hin : G.inF (devCoeff Φ f m) = G.inF (Φ * (B - E)) := by
      rw [e2]
      exact hloc _ _ hkey
    -- (V2a)'s divisibility block fires at the vertex slot: contradiction
    exact hV2a (devCoeff Φ f m) hCm0
      (devCoeff_natDegree_lt hmon hdeg f m) ⟨B - E, hin⟩
  -- (V2c) fires: gd3_min pins the graded order at μ; the two orders tie
  have hgrμ : GrOrdAt G Φ f μ := gd3_min G Φ hkpa ψ Rlam A f hf μ hres
  have hmμ : m = μ := GrOrdAt.unique hgrm hgrμ
  refine ⟨hA, ?_, ?_, ?_⟩
  · rw [← hmμ]
    exact hum
  · intro k hk
    rw [← hmμ] at hk
    have hkr : k ∈ Finset.range (f.natDegree + 1) := by
      have hm' := Finset.mem_range.mp hmrange
      exact Finset.mem_range.mpr (by omega)
    refine lt_of_le_of_ne (ha k hkr) fun h => ?_
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨hkr, h.symm⟩
    have := hmle k hkS
    omega
  · rw [← hmμ]
    exact hCm0

/-- Lemma WGEO over the named key-compliance rows (V1) = MacLaneV1Pkg,
    (V2a) = KeyPkg.KPa, (V2b) = devid, (V2c) = gd3_min — the GD23 re-founding.

    O-1thr rev 4 §2.5 Lemma WGEO, clauses (a)/(b), at the state
    `(w (i+1), keys i)` (the `tie_w_eq_v` index dictionary): with
    `C_k := devCoeff (keys i) f k`, `u_k := w(C_k) + k·w(keys i)` and
    `γ := w (i+1) f`, (a) every inhabited slot sits on or above the side
    value, and (b) the sheared minimum is FIRST attained exactly at
    `μ = ord_ψ(R_λ f)`: `u_μ = γ` (in particular `C_μ ≠ 0`) and `u_k > γ` at
    every `k < μ`.  See the section header for the full completion ledger
    (row provenance, why `hloc`/`hsep` are displayed rows, and the (c)/(d)
    scope record); proof = the `wgeo_core` kernel fired at the state, with
    (V1) consumed as its level-(i+1) row set and (V2a)'s `monic`/
    `positiveDegree` rows fired directly. -/
theorem wgeo {p : ℕ} [Fact p.Prime]
    (w : ℕ → Polynomial ℤ_[p] → WithTop ℤ) (keys : ℕ → Polynomial ℤ_[p])
    (i : ℕ)
    (hv1 : MacLaneV1Pkg w keys)
    (hkp : KeyPkg (w (i + 1)) (keys i))
    (G : ValGr (w (i + 1)))
    (hkpa : KPaBlock (w (i + 1)) G (keys i))
    (hV2a : ∀ B : Polynomial ℤ_[p], B ≠ 0 → B.natDegree < (keys i).natDegree →
      ¬ ∃ C : Polynomial ℤ_[p], G.inF B = G.inF (keys i * C))
    (hloc : ∀ X Y : Polynomial ℤ_[p],
      w (i + 1) X < w (i + 1) Y → G.inF (X + Y) = G.inF X)
    (hsep : ∀ X Y : Polynomial ℤ_[p], w (i + 1) X ≠ ⊤ →
      G.inF X = G.inF Y → w (i + 1) X < w (i + 1) (X - Y))
    (hdev : ∀ B : Polynomial ℤ_[p], B ≠ 0 →
      w (i + 1) B = minDev (w (i + 1)) (keys i) B)
    {𝒦 : Type*} [Field 𝒦] (ψ : Polynomial 𝒦)
    (Rlam : Polynomial ℤ_[p] → Polynomial 𝒦)
    (A : AnchoredRead G (keys i) ψ Rlam)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (htop : w (i + 1) f ≠ ⊤)
    (μ : ℕ) (hres : Moves.OrdPsiPoly ψ (Rlam f) μ) :
    (∀ k, devCoeff (keys i) f k ≠ 0 →
      w (i + 1) f ≤
        w (i + 1) (devCoeff (keys i) f k) + k • w (i + 1) (keys i)) ∧
    w (i + 1) (devCoeff (keys i) f μ) + μ • w (i + 1) (keys i) = w (i + 1) f ∧
    (∀ k, k < μ →
      w (i + 1) f <
        w (i + 1) (devCoeff (keys i) f k) + k • w (i + 1) (keys i)) ∧
    devCoeff (keys i) f μ ≠ 0 :=
  wgeo_core (w (i + 1))
    ⟨hv1.zero (i + 1), hv1.one (i + 1), hv1.mul (i + 1), hv1.add (i + 1)⟩
    (keys i) hkp.monic hkp.positiveDegree G hkpa hV2a hloc hsep hdev
    ψ Rlam A f hf htop μ hres

end UnitIIIT13

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-T15 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.vtx_htUpper_div

-- Footprint audit (unit III-T11a gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.m6c_beyondWindow_e1

-- Footprint audit (unit III-T12): the support extraction expects Lean core
-- only; `m6c_noPhantom` carries the confinement leg's honest sorry — expect
-- `sorryAx` there until III-T11b/III-T13 land (BLOCKED note at the leg).
#print axioms LeanUrat.Scaffold.DictIII.lastRead_of_readsOf_snoc
#print axioms LeanUrat.Scaffold.DictIII.m6c_noPhantom

-- Footprint audit (unit III-T13 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.wgeo
