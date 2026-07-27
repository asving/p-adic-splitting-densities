# FABLE CONFIRMING PASS — §M-SPECIES rev 7 (2026-07-27)

Verifier: fresh Fable instance (dual-acceptance shot, Fable half; predecessor
FABLE_VERIFY_MSP_2026-07-27.md CLEAN-at-content on rev 6 with 2 display gaps
F1/F2; rev 7 = commit 614ca0d, exactly those repairs). Text: live §M-SPECIES,
MOVES_2026-07-24.md ('## §M-SPECIES' → '## §T-ASSEMBLY').

## Skeleton
- S1 The two rev-7 fixes: quote + verify ................... [filled below]
- S2 Drift-prone-citation sweep (whole section) ............ [filled below]
- S3 Fresh-angle sweep: menu-map completeness, (B1)-(B5)
     derivations, worked witnesses, Q3 group ............... [filled below]
- S4 Own-construction check (python, /tmp) ................. [filled below]
- S5 Findings + verdict .................................... [filled below]

## S1 — The two rev-7 fixes (commit 614ca0d), quoted and verified
FIX 1 (predecessor F1, grep anchors) — APPLIED, INCOMPLETE AT REV 7:
  "— each quote locatable BY ITS TEXT (grep anchors; line numbers drift as
  the file grows and are deliberately not cited):" [n=1 clause head]
  Three of five VP cites converted (τ-irr domain, covering line, τ-hen);
  TWO bracketed cites survived rev 7: "[(c2) MUTUAL EXCLUSIVITY, lines
  7102–7103]" and "[lines 7106–7109]" — both STALE vs live VP (actual
  7110–7111 and 7115–7116) and inconsistent with the just-declared policy.
  ADJUDICATION: caught in parallel and repaired as REV 8 (commit b540ebd,
  03:36, "the two wrapped drift-prone citations → grep anchors") DURING this
  pass. Current live section: ZERO line-number cites (sweep S2). All five
  quotes re-checked VERBATIM against live VP-2/(c2) text.
FIX 2 (predecessor F2, 47 → 45) — APPLIED, CORRECT:
  "all 45 fresh N* thresholds SHARP from both sides
  (45, not 47: the two {(1,1)³} rows carry no N* — field-size-excluded at
  every level...)". Arithmetic re-derived: 53 − 2 field-size-excluded = 51
  N*₃-carrying; 51 − 6 diagnosed = 45 fresh; consistent with the display
  "the other 45 of the 51 letters passing (1) at p = 3".

## S2 — Drift-prone-citation sweep
Rev-7 blob ('§M-SPECIES'→'§T-ASSEMBLY'): exactly the two residual cites
above, nothing else. Current (rev-8) text: 0 matches for line-number cites.
No other stale-reference class found (dates, gate names, file cites checked).

## S3 — Fresh angle (what the predecessor did not probe)
(B1)–(B5) DERIVATIONS re-checked against §B2-DEF: (B1) log₂ n increments
from ∏eᵢgᵢ ≤ n, each genuine factor ≥ 2 ✓; (B2) w_r ≤ n via w_r = ∏gᵢ ≤
∏eᵢgᵢ ≤ n ✓; (B4)'s w′·D ≤ n via w′ ≤ W ≤ ⌊n/D⌋ (B3) ✓; d ≤ w′+1 auto
(d = ℓ+1 ≤ eℓ+1) ✓. WORKED WITNESSES recomputed by hand: f = x³+x²+x+2,
p=2: f̄ = z(z²+z+1), NP points (0,1),(1,0)..(3,0), slope-0 side [1,3],
R_anch = z²+z+1 irreducible/F₂ → R5 {(2,1)}▸(2,1), a=1, left flank (1) →
I(2,2) ✓. f = x³−3x²+3x−3, p=2: f̄ = (z+1)³ → R6 ▸(1,3); shift x→x+1 gives
x³−2, NP (0,1)–(3,0) slope 1/3 → Q3 e=3 letter → I(3,1) ✓. MENU MAP
completeness by hand: 7 continuing-edge classes exhaust all sels over the
53; Q3-group identity (POST-REC (1,1,3) ≡ ROOT rows) from the constraints'
(D,w,W)-dependence only ✓.

## S4 — Own construction (python, /tmp/msp_enum.py)
Catalogue re-built from the DEFINITION alone ((G5)-closure from ROOT stage;
per stage: (e,ℓ,s₀′) with s₀′+eℓ ≤ W, a = ⌊s₀′/e⌋, a+ℓ ≤ W; λ multisets
Σgμ = ℓ; sel ∈ λ; flank compositions; (G6) at W=1). OUTPUT: 8 stages =
exactly the displayed five groups; counts 21/21/6/1/(1+1+1+1) = 53 EXACT.
Self-loops: exactly 2 (Q3 {(1,3)}▸(1,3), Q2 {(1,2)}▸(1,2)) ✓. SP-DAG rank
ρ strictly increases on ALL non-loop SUCC edges (0 violations over the full
graph); full letters unique per stage (3 total) — (i) confirmed. Edge-class
targets reproduce the sealed menu map exactly (7/7).

## S5 — Findings and verdict
 F1 [GAP, display — MOOT AT REV 8]: rev 7's F1 repair was incomplete (the
    two surviving bracketed cites, S1); independently caught and repaired
    in place as rev 8 mid-pass. No content effect; quotes verbatim.
 No criticals. Both commissioned fixes genuine; catalogue, menus, budgets,
 SP-DAG, witnesses independently reconstructed or re-derived.
VERDICT: CLEAN on the current rev-8 text (0 critical, 0 gaps). Rev 7
as-committed carried the one display residue above (superseded).
