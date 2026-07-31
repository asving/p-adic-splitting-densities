/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG15_siteData

/-!
# IB-G15b — the (e4) FIRST-INDEX SEAM, typed visible (bridge BP1, D-SC.8)

Scope fold-in per the item-9 FORM ADJUDICATION (2026-07-31, wf_b933dcd7-877,
`notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` sign-off item 9(iv)): "the
base-change seam (REL.2(d), e_j ambient-vs-rebased) is note-side OPEN — the
(e4) 'owed' first-index definition joins the carrier-layer design scope."

THE NOTE'S OWN STATUS (MOVES_2026-07-24.md 9524–9528, (e4)): the entry's first
index e_j is defined FROM b_j's DATA — "candidate: (a2)'s O_{δ_j}-degree
d_j^rel — OWED, NOT ASSUMED".  The parked draft's CF13 repair DEMOTED the
candidate to a named definition NO consumer may hypothesize; the (e4)
OBLIGATION is `tableConv entryFirst` ([3]'s exported convention) ALONE.  This
unit carries that discipline to the sited carrier layer and makes the OPEN
ambient-vs-rebased seam VISIBLE as vocabulary: BOTH candidate readings are
named below — the REBASED reading (e_j = d_j^rel, the note's own candidate)
and the AMBIENT reading (e_j = d_j, the un-rebased O_δ-degree the item-9
countermodel analysis surfaced as the seam's other face) — so the future
(e)-pass resolves the seam by PROVING one of them from [3]'s tables (or
refuting both), never by a silent keying choice.

CONSUMPTION FENCE (CF13, verbatim discipline): these are NAMED CANDIDATES
ONLY.  NO consumer may hypothesize either; no `SitedSlot_*` law references
them; the (e4) conjunct of `SitedSlot_rel2e` and the keying clause of
`SitedSlot_rel3` read `tableConv`/`entryFirst` exclusively.  IB-G20's closure
manifest flags any violator.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

/-- (e4) CANDIDATE, REBASED reading (the note's own: "candidate: (a2)'s
O_{δ_j}-degree d_j^rel — owed, not assumed"; CF13-demoted): the branch's first
index is the RE-BASED target degree.  NAMED CANDIDATE ONLY — no consumer may
hypothesize it (file-header fence). -/
def SiteBeta.firstIdxCandidateRebased {p : ℕ} [Fact p.Prime] {S : RelSite p}
    {Sp : SpeciesSyntax} {Dc : SiteDict p S Sp} (B : SiteBeta p S Sp Dc) : Prop :=
  B.entryFirst = S.dRel

/-- (e4) CANDIDATE, AMBIENT reading (the seam's other face, item-9(iv): e_j
read as the un-rebased O_δ-degree d_j of b_j's cluster).  NAMED CANDIDATE ONLY
— no consumer may hypothesize it (file-header fence).  The ambient-vs-rebased
choice is note-side OPEN; [3]'s exported `tableConv` is the only (e4)
obligation until the (e)-pass proves one reading. -/
def SiteBeta.firstIdxCandidateAmbient {p : ℕ} [Fact p.Prime] {S : RelSite p}
    {Sp : SpeciesSyntax} {Dc : SiteDict p S Sp} (B : SiteBeta p S Sp Dc) : Prop :=
  B.entryFirst = (S.d : ℕ)

end LeanUrat.MovesU
