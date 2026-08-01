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
