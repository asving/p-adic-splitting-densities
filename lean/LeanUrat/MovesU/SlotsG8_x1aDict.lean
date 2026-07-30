/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-G8 — Slot_x1aDict FORMULATION SKELETON (bridge BP1, §3.8)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (the
x1aDict row) + §4 group G (IB-G8: "Slot_x1aDict (GMN-axiom-citing; faithfulness
entry cross-ref). ADJ→H") and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
(BP1 Q5).

THE RESERVED PARAMETER (U10_theoremU.lean:80–81, verbatim): "`x1aDict` — CL-15's
per-species GMN index dictionary beyond the typed ALIGN face `KT.cl15_align`
(owner [5])" — one of the thirteen wave-4-boundary bare-Prop parameters
(UNPINNED pending this carrier).  DefsLedger's `UpstreamTyped.cl15_align`
(DefsLedger.lean:175) types the operative ALIGN layer at the certified-increment
state — `MovesX.X1aAlignP n KC.XF ⟨true, false⟩` (MovesX/Defs.lean:362:
"d_cert(H) ≤ ind(f) on every stratum, off disc = 0"); "the per-species GMN index
dictionary itself is a bare parameter" (its docstring, verbatim).

FORMULATION TARGET (H-phase; deps: `KernelCarriers` (the MovesX family `KC.XF`
with its `GMNIndex` `ind`, MovesX/Defs.lean:205, + the species syntax `KC.Sp`);
owner [5]; note display CL-15 "dictionary beyond ALIGN"): the PER-SPECIES GMN
INDEX DICTIONARY — a per-species-letter decomposition of the GMN index
`(KC.XF.gmn p).ind f` along the stratum history's node species, such that the
certified-increment charges `X1aAlignP` counts (`dCert ⟨true, false⟩`,
MovesX/Defs.lean:105) are priced letter-by-letter into index contributions
(each certified node's species letter carries a positive index share, shares
summing ≤ ind f) — turning the typed aggregate ALIGN face into the note's
per-species ledger.  The dictionary carrier (letter → index-share map) has NO
built vocabulary — the H-phase designs it as bound data INSIDE the Prop (per
§3.8's "newly-designed carrier vocabulary").

THE TRUSTED-AXIOM CITE (this is THE ONLY slot allowed to reference the declared
GMN axiom — §3.8, verbatim): the GMN theorem of the index enters the built
corpus as the DECLARED NAMED-CITE axiom
`LeanUrat.OM.omReadValuation_lt_of_certLevel_fkeyed` (OM/Classifier.lean:1128;
GMN Cor 4.19 / Thm 4.18, Guàrdia–Montes–Nart arXiv:0807.2620, the read-set-
restricted `ind(f) ≤ v_p(disc f)` face) — faithfulness entry **AX-INDEX** in
`docs/AXIOM_FAITHFULNESS.md` (§"AX-INDEX", FAITHFUL (narrowly scoped), DRAFT
2026-07-30 pending Asvin review; guardian audit `notes/SEMANTIC_AUDIT_LOG.md`
AXIOMS section).  The H-phase Prop may CITE this axiom's index reading when
tying the dictionary to `GMNIndex.p2`'s `2·ind f ≤ vdisc f` surface; per the
axiom policy the cite must stay statement-side (the slot is a Prop — consuming
the axiom in a PROOF on the capstone path would change the capstone footprint
and is a stop-the-line event; the bridged capstone's expected footprint note
must disclose any such consumption).

E-PHASE DIVISION OF LABOR (as in IB-G2, per §3.8/R9): body `sorry`; the
displayed Prop is the ADJ→H deliverable behind the Q5 Codex-audit gate.
NON-VACUITY DUTY (IB-G11c): `example : ¬ Slot_x1aDict degenerate…` — e.g. FALSE
for a dictionary assigning zero shares while certified charges exist.
CLOSURE MANIFEST DUTY (IB-G12): every identifier → built decl path.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
H-PHASE RESOLUTIONS (2026-07-30, cluster BP1-P10-slots; FLAGGED for the Q5 Codex
audit):
* (h1) THE DICTIONARY CARRIER is ∃-bound per stratum history: a species-letter
  assignment `letterOf : positions → KC.Sp.Letter` PLUS an index-share map
  `share : positions → ℕ`.  The letter is PINNED to the node's OWN stage tuple
  through the built grammar anchor `SpeciesSyntax.shape` (letters are "DEFINED BY
  stage tuples (e, h, g, μ)"): at a continuing node with selection `(g, μ)`, the
  assigned letter's shape IS `(e, h, g, μ)` — the node's own read, never a
  re-key.  This constrains `KC.Sp` to realize every stratum stage tuple — content
  strictly beyond the aggregate ALIGN face.
* (h2) LETTER-BY-LETTER PRICING: every certified charge (the `dCert ⟨true, false⟩`
  population `cl15_align` counts — certified increments) carries a POSITIVE index
  share, and the shares sum within the GMN index `(KC.XF.gmn p).ind f`.  The ∃
  therefore IMPLIES the ALIGN face `dCert ⟨true, false⟩ H ≤ ind f` (each certified
  node contributes ≥ 1 to the sum) — "beyond ALIGN" with ALIGN recoverable, never
  contradicted.
* (h3) THE AXIOM CITE stays statement-side, per the file header: this Prop TYPES
  the dictionary against `GMNIndex.ind`; the index's discriminant surface
  (`GMNIndex.p2`: `2·ind f ≤ vdisc f`) is the carried structure law, and the
  read-set-restricted GMN face is the DECLARED axiom
  `LeanUrat.OM.omReadValuation_lt_of_certLevel_fkeyed` (AX-INDEX) — cited here,
  consumed by no proof in this file.
NON-VACUITY (IB-G11c's duty, follow-up file): FALSE at a degenerate instance
whose `gmn` assigns index 0 while a stratum history carries a certified charge
(zero shares ∧ positive-charge duty clash — the file-header example).
-/

namespace LeanUrat.MovesU

/-- IB-G8 — **`Slot_x1aDict`** (CL-15's per-species GMN index dictionary beyond
the typed ALIGN face `KT.cl15_align`, owner [5]; the ONLY slot allowed to
reference the declared GMN axiom — AX-INDEX, `docs/AXIOM_FAITHFULNESS.md`): the
per-species-letter decomposition of `(KC.XF.gmn p).ind` pricing the certified
ALIGN charges letter-by-letter (see the file header for the formulation target
and the axiom-cite discipline).  H-phase fills the displayed Prop; Codex audit
before any consumer (Q5). -/
def Slot_x1aDict (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p) (H : MovesX.XHistory n),
    f ∉ MovesX.discZero n p → (KC.XF.gmn p).inStratum f H →
    ∃ (letterOf : Fin H.length → KC.Sp.Letter) (share : Fin H.length → ℕ),
      -- (h1) the dictionary keys each node by its OWN stage tuple:
      (∀ (i : Fin H.length) (g μ : ℕ), (H.get i).sel = some (g, μ) →
        KC.Sp.shape (letterOf i) = ((H.get i).e, (H.get i).h, g, μ)) ∧
      -- (h2) every certified ALIGN charge carries a positive per-letter share:
      (∀ i : Fin H.length,
        MovesX.certified ⟨true, false⟩ (H.get i) = true → 1 ≤ share i) ∧
      -- (h2) the shares decompose within the GMN index:
      ∑ i : Fin H.length, share i ≤ (KC.XF.gmn p).ind f

end LeanUrat.MovesU
