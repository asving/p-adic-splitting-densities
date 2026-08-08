# HMENU3 DATED ANNEX — DRAFT for the orchestrator (written by the W-12 r5 unit, 2026-08-08)

**What this file is.** The verbatim text of a dated annex to
`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md`, correcting THEOREM
HM3.C's (A0) quantifier phrase to the disc ≠ 0 form. HMENU3 is ACCEPTED
at 2/2 and carries a FREEZE-CONVENTION STAMP ("the accepted text is the
post-r2 body, byte-frozen since e1280be … dated appends only
hereafter"), so this correction is a DATED APPEND, not an in-place edit:
the frozen body stays byte-identical and the annex is the correction of
record.

**Where to apply it.** Append the block below verbatim at the END of
HMENU3_PROOF_2026-08-08.md, after the ★ ACCEPTANCE RECORD ★ section.
Nothing above it is edited.

**Scope discipline (read before applying).** HM3.C's CONCLUSION stands.
Only the quantifier phrase at two sites is corrected. No count, no law,
no box, no grade and no corollary moves; the acceptance at 2/2 stands at
the corrected quantifier.

---

## ▼▼▼ THE ANNEX TEXT (append verbatim below the acceptance record) ▼▼▼

## ANNEX A (dated append, 2026-08-08, post-acceptance; the frozen post-r2 body above is NOT edited): THEOREM HM3.C's (A0) quantifier corrected to the disc ≠ 0 form

**Raised by W-12's hostile arc.** W-12's r4 repair (**d2d91b7**) struck
the same unrestricted quantifier from W-12 §S2.3 as FALSE in equal
characteristic at wild decided shapes; W-12's PE5 pass (**c3e2f8e**,
FINDING 1) then observed that W-12's own [r4] FIRING CHECK was vouching
for THIS note's phrasing of it, and W-12's r5 repair re-worded that row
and recorded the blast-radius sweep that reached here. The defect
entered through the S2.3-era phrasing the two notes SHARED — HM3.C's
own cited warrant for the sentence is "W-12 S2.3 at the terminal
frame", i.e. the pre-r4 S2.3 text — so it is inherited, not
independently generated.

**The two sites, quoted, and their corrected readings.**

1. **§S1, THEOREM HM3.C, the (A0) clause (L216–219).** As frozen: "(A0):
   every menu member is conservative-DECIDED — all consulted data
   in-window with separable residuals — **so Ore certifies EVERY lift**
   (W-12 S2.3 at the terminal frame; W12-L1(c) transports the DBL
   certificates); σ_F = the leaf table." **Read as:** "… so Ore
   certifies every lift **with disc ≠ 0** …". 
2. **§S5.2 ((A0), the proof, L431–437).** As frozen: "Ore (W-12 S2.3)
   then assigns the SAME σ to every O-lift **(not only disc ≠ 0 ones)**
   at the terminal frame". **Read as:** "… assigns the SAME σ to every
   O-lift **with disc ≠ 0** at the terminal frame", the parenthetical
   WITHDRAWN.

**Why the unrestricted form is false — a counter-instance inside this
note's own menu.** Take TRP-RAM3(1), one of the seven depth-0 TRP
families THEOREM HM3.B aggregates. Its members with b₂ = b₁ = 0
in-window and v(b₀) = 1 exist at every window N ≥ 2. Over F_q[[t]] with
p = 3, the lift F = y³ + b₀ has F′ = 3y² ≡ 0, hence gcd(F, F′) = F and
disc F = 0: F = (y + b₀^{1/3})³ is inseparable, so it has NO splitting
type σ at all and Ore certifies it for no σ. The member is
conservative-DECIDED all the same (all consulted data in-window,
separable residuals), so decidedness is untouched — it is exactly the
LIFT quantifier that must exclude disc = 0.

**What the corrected clause says, and that it is the clause consumed.**
Corrected (A0) at n = 3: *every window member of every core-menu family
is conservative-DECIDED, and every disc ≠ 0 lift of that member has
σ = the leaf table's entry.* This is (i) exactly W-12's W12-BOX-7 pinned
notion ("Decided = certified on window digits for all disc ≠ 0 lifts"),
(ii) exactly what W-12.D's (A1) σ-LABELING clause and BOTH Step-4 bounds
consume (they quantify over disc ≠ 0 lifts only; the disc = 0 locus is a
null set handled by Step 4's classical part), and (iii) already how THIS
NOTE states (A0) in §S0: "(A0): every window member of a core family has
ALL its **disc ≠ 0** lifts of the family's σ" (L75–76). The note's
intended content was the disc ≠ 0 form throughout; two sites over-reached
in phrasing.

**What does NOT move.** THEOREM HM3.A (history-resolved exact laws),
THEOREM HM3.B (the finite (A1)-admissible menu and its instance
bracket), HM3.C's (A2) exact complement r(N) = q(q−1)q^{N−1}·[⌊(N−1)/2⌋
(q−1)q^{N−2} + q^{N−1}] + q·u(q,N) with r(N)/q^{3N} → 0, §S5.4's
"(A0) is quantified over CORE members only" argument, COROLLARY HM3.D's
five cubic R_τ(q) with Σ_τ R_τ = 1 in both characteristics, W12-BOX-2's
discharge of (hMenu-3) at composition grade (and its verbatim §S8.1
annex block, applied at W-12 as ANNEX 2), every honest box HM3-BOX-1…5,
and every number in the sealed battery (41 rows, 183,387 checks,
0 violations, teeth 21/15/10/4, 9,952 PARI-scored deep-decided members):
all UNCHANGED. Nothing in this note, in W-12.D, or in the W-12 r5
FIRING CHECK quantifies over disc = 0 lifts, so **W-12.D's n = 3 firing
stands on the corrected form** — verified at W-12 PE5 (c3e2f8e) and
recorded in W-12's [r5] NOTICE at its ANNEX 2.

**Machine status: blind, not wrong — and blind by construction.**
HM3-ORACLE's PARI σ-leg runs on mixed-characteristic ℤ_p rows only
((p,N) = (2,5), (2,6), (2,7), (3,5)) — the coverage limit already
disclosed at HM3-BOX-3 ("Oracle: mixed-characteristic only", inheriting
W10-BOX-4/W11-BOX-4). Over ℤ₃ the same shape y³ + b₀ has
disc = −27b₀² ≠ 0, so the equal-characteristic disc = 0 lift never
enters the scored set: no oracle verdict was wrong, and none was
evidence about the unrestricted quantifier either. Same structure as
W-12's BOX-6 disclosure at its own S3.2 witness repair. Runner and
artifacts stay byte-frozen at the HMENU3 seal (64d3ff9 / verdict
625fa49).

**Grade and acceptance.** This annex changes no statement's content and
no proof step: it corrects a quantifier PHRASE at two sites and withdraws
one parenthetical. The 2/2 acceptance recorded above stands, read at the
corrected quantifier. Cross-references: W-12 §S2.3's [r4] strike with
its counter-instance (d2d91b7); W-12's [r5] rewording of the n = 3
FIRING CHECK row and its [r5] NOTICE ON ANNEX 2, which carries the m2
blast-radius sweep (six surfaces; HEX3_PROOF L80–81 carries the same
loose phrasing with its U₃^σ ≤ U₃^conv conclusion UNAFFECTED, a phrasing
correction owed at HEX3's own arc; GENH4.C/GENHN.C are already stated
with "EVERY lift with disc ≠ 0"); W-12 PE5's verification that HM3.C's
substance and all counts survive (c3e2f8e).

## ▲▲▲ END OF ANNEX TEXT ▲▲▲

---

**Provenance of this draft.** Written by the W-12 r5 repair unit,
2026-08-08, as the HMENU3-side half of W-12 PE5 FINDING 1. Every quoted
HMENU3 line was verified byte-faithful against
HMENU3_PROOF_2026-08-08.md at HEAD before drafting (L75–76 §S0's (A0);
L216–219 §S1's HM3.C; L431–437 §S5.2; HM3-BOX-3's oracle scope; the
acceptance record's freeze stamp), and the runner's oracle rows were
read from `verification/openmath/hmenu3_checks.py` (`ORACLE_ROWS =
[(2, 5), (2, 6), (2, 7), (3, 5)]`, ℤ_p). Application (and any wording
change) is the orchestrator's call; this file is a draft, not an applied
edit.
