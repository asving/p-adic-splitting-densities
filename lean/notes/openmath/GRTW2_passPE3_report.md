# GRTW2 passPE3 report — hostile pass 3 on `GRTW2_PROOF_2026-08-08.md` (post-r2; acceptance attempt)

**Verifier:** Fable hostile pass PE3, fresh context, wallclock 2026-08-07.
**Target:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` at HEAD (last note
commit ffa1e57 = the r2 repair round; working tree byte-clean). **Inputs read:**
the PE1 report (083adff), the PE2 report (79e796b), the full r2 diff
(79e796b → ffa1e57, note-only +225/−38), the GMN print
`docs/references/HigherNewton.tex` at the cited anchors (line-exact), the
sealed runner + committed artifacts + the sealed probe leg, the WM/JB consumer
surfaces. I fixed nothing.

## VERDICT

**0 CRITICAL ERRORS. 1 JUSTIFICATION GAP (minor). 0 other defects. NOT
CLEAN — the counter stays 0/2** (this pass does not start the 2-clean count).
Everything the r2 round SET OUT to do is done correctly: LEMMA W2-ID1 is
correctly stated and its proof is sound (re-derived, §A.1); (OPEN-2a) is
exactly the m ≥ 2 inductive step the re-scope warrant consumes (§A.2); the
38/44 = 36+2 census is exact (recomputed from the committed JSON by my own
is-one test, §A.3); the P2 sign REVERT is faithful to tex 1431 at source
(re-derived from the print, all four anchors line-exact, §A.4) and the
anti-re-flip records are adequate (§A.5); the machine leg reproduces (exit 0,
bit-identical mod three timing figures, §B); a fresh leg by an unused route
confirms the §3.4 closed form at FULL roster scope (§C). The one gap: the
r2 text claims the two-sided identification "first recorded ξ ≠ 1 junction =
first byte-divergence" is **PROVED at m = 1**, but LEMMA W2-ID1 proves only
ONE direction of it; the converse rides an unpinned recorded-pair selection
rule, and under the sealed runner's actual scan semantics there is a concrete
class-pin counter-instance at m = 1 (constructed and machine-probed, §P1).

---

## P1 — JUSTIFICATION GAP (minor; CONFIRMED by construction + probe). The two-sided "identification PROVED at m = 1" claims outrun LEMMA W2-ID1, which proves one direction; the converse depends on a recorded-pair selection rule the note never pins, and the sealed runner's own scan violates it off-roster.

Quotes (all [r2] text). W2-ID1's closing sentence (§5.2): "*Consequently the
identification 'first recorded ξ ≠ 1 junction = first byte-divergence' is
**PROVED** for every junction whose strictly-below junctions all sit at
m ≤ 1 (ascending: r = 2 by TH-BASE, r = 3 by this lemma)*". Grade cap
[r2, P1]: "*that this coincides with the first BYTE-divergence is PROVED at
m = 1 (LEMMA W2-ID1, §5.2)*". §6.2 W2-C3 row: "*the coincidence with first
byte-divergence is W2-ID1 at m = 1*". S-STATUS / §8 P1(a): "*its m = 1 case
PROVED*". Also consuming the converse silently: W2-OPEN-2's premise clause
"*byte-DIFFERENT for r₀ ≤ q < r*" (byte-RED AT r₀ is the converse direction,
not covered by the (OPEN-2a) sub-clause, which is the forward direction only).

**What W2-ID1 actually proves (correct, re-derived §A.1):** recorded ξ = 1 ⟹
byte-equal, at m = 1. That gives HALF the identification: no byte-divergence
strictly below the first recorded twist. The "=" additionally needs the
converse — **recorded ξ ≠ 1 ⟹ byte-RED** — and that is NOT a theorem of the
note: at a byte-equal junction the trivial pair (1, c) always satisfies the
orbit equations (Thm-`phir`), so the converse holds iff the recording
PREFERS ξ = 1 when a trivial pair exists. The note pins no such rule; its own
§3.4 rk. 2 states the pair is non-unique on sparse support, and §5.1 step 1
just says "record the junction pair". The note's machine bracket for the
ledger — the sealed `orbit_scan` (grt_w2_checks.py lines 135–164) — records
the FIRST satisfying ξ in `F.elems()` enumeration order, and for extension
residue fields that order yields the generator BEFORE 1 (`Ext.elems` =
`itertools.product(base.elems(), repeat=g)`: for F₄, (0,1) = ζ precedes
(1,0) = 1).

**Class-pin counter-instance at m = 1 (roster-invisible).** Tower: ℤ₂ (or
F₂[[t]]), d₀ = 1, Φ₀ = x; read 0 = (e₀,h₀,g₀) = (1,1,2) with ψ₀ = y²+y+1
(K₁ = F₄, ζ := z₁); read 1 = (2,1,3) with ψ₁ = y³ + ζ (monic, irreducible —
x³ = 1 for all x ∈ F₄* so no root, and a cubic factorization needs a root —
ψ₁(0) = ζ ≠ 0; in the [ILN]† S0.1 pin). At the m = 1 junction: e₀ = 1 ⟹
ℓ₀ = 0 ⟹ A₁ = 0 ⟹ c = 1 and the §3.4 rk. 3 byte law holds trivially — the
junction is **byte-equal**, formula pair (1,1). But supp(ψ₁) = {0,3} and
ξ³ = 1 for EVERY ξ ∈ F₄*, so all three units satisfy the orbit equations,
and the sealed scan's enumeration records **(ζ, 1) — recorded ξ ≠ 1 at a
byte-equal junction**. The ledger's r₀ sits at r = 3 with NO byte-divergence
anywhere; "first recorded ξ ≠ 1 = first byte-divergence" is FALSE; the
transport fires a spurious conjugation (ψ^tw = ψ since ζ stabilizes the
support, but the step-2 re-coordination (a_i) ↦ (a_i·ζ^i) of higher data is
nontrivial). Machine-probed with the scan's ξ-loop semantics copied verbatim
(`/tmp/w2_pe3_fresh.py`, scan-order probe: enum order [(0,0),(0,1),(1,0),
(1,1)], recorded pair ((0,1),(1,0)) = (ζ,1), trivial pair also satisfies).
**Why no roster instance shows it:** the Tower builder implements only
g ∈ {1,2} ("only g in {1,2} implemented", iterlawn_pe_reimpl.py), and for
g_m ≤ 2 no support-stabilizing unit with zero constant coefficient exists
(g=1: stabilizer trivial; g=2 sparse: stabilizer {±1}, and ±1 have nonzero
constant term, enumerated after 1 only when equal to 1) — so on this roster
enumeration order coincides with the ξ=1 preference everywhere, consistent
with the 22/22 census. The failure needs g_m ≥ 3.

**Blast radius: contained.** Every consuming surface uses only the PROVED
direction: the §5.2 re-scope warrant sentence states the needed step
precisely as "recorded ξ = 1 ⟹ byte-equal ... PROVED at m = 1"; (OPEN-2a)
is stated one-directionally; the 36+2 census consumes only below-chain
byte-share (§A.3). Under a trivial-preferring selection rule the converse
becomes easy at EVERY m (byte-equal ⟹ R = c·ψ ⟹ trivial pair exists ⟹
recorded ξ = 1 under preference), so the intended claim is true under the
natural convention — the defect is that the convention is never displayed
while the note's own sealed scan implements a different one. Repair: one
honest sentence — either scope the four "identification PROVED / coincidence"
sites to the proved direction ("no byte-divergence strictly below the first
recorded twist"), or pin the §5.1 recorded-pair convention to prefer ξ = 1
and disclose that the sealed scan's enumeration order implements the
preference only over prime-field layers (unobservable on the g ≤ 2 roster);
and flag the converse direction inside W2-OPEN-2's "byte-DIFFERENT for
r₀ ≤ q" premise clause alongside (OPEN-2a). (Corollary for the record: PE2's
P1 aside "one direction is easy (recorded ξ ≠ 1 ⟹ byte-RED)" was itself
true only under the unpinned preference.)

---

## §A. The charge items — checked and CONFIRMED

**A.1 LEMMA W2-ID1 re-derived (the m = 1 proof from the §3.4 display) —
SOUND.** Premises verified: at m = 1 the §3.4 display is unconditional
(W2-C2(a) machine CK-SLOT-M1 16/16; shared-key below holds by TH-BASE; no
transport can fire below r = 3 — `transport_leg` loops r from 3, and ψ^cur =
ψ₁). Display: R₂(Φ₂^har)(y) = ψ₁(ξ_f·y), (ξ_f, w_f) = (z₁^{−e₁A₁}, 1) —
exactly §3.4 at m = 1 (χ₁ = 1). The steps: recorded (1, w) gives R₂ = w·ψ₁;
j = 0 coefficient with ψ₁(0) ≠ 0 (class pin) forces w = 1; coefficientwise
ψ₁,j·ξ_f^j = ψ₁,j gives ξ_f^j = 1 on supp(ψ₁), including j = g₁ (monic top
∈ supp); then c·z₁^{A₁e₁j} = ξ_f^{g₁}·ξ_f^{−j} = 1 on supp ∩ [0, g₁) using
c = c₁^{e₁g₁} = z₁^{−A₁e₁g₁} = ξ_f^{g₁} (c₁ = z₁^{−A₁}, §1.3) and
z₁^{A₁e₁j} = ξ_f^{−j} — which is §3.4 rk. 3's m = 1 byte-equality law, an
iff, so byte-equal. Each identity re-checked; the proof is valid for ANY
recorded pair with ξ = 1 (non-uniqueness harmless in this direction). The
lemma's machine line (22/22 walked equivalence, m = 1 slice = 16 r = 3 rows)
independently recomputed from the JSON: 22 walked + 6 SKIP, m = 1 slice 16,
recorded-ξ-trivial ⟺ byte-equal with 0 exceptions, every below-r₀ junction
byte-GREEN. The claims-table W2-ID1 row states the one-direction form —
accurate. Only the "Consequently" extension overruns (P1).

**A.2 (OPEN-2a) audited against the re-scope warrant — EXACTLY the needed
premise sub-clause.** The warrant needs, ascending through each junction
q < r₀ of a transported chamber: below-q byte-shared (induction) + recorded
ξ = 1 at q ⟹ raw print key byte-equal to harness key at q; base r = 2 =
TH-BASE, m = 1 step = W2-ID1, m ≥ 2 step = verbatim the sub-clause statement
"at a junction at level m+1 with m ≥ 2, keys below byte-shared and recorded
ξ = 1, the raw print key is byte-equal to the harness key". Nothing weaker
suffices (the read-invisible-divergence genre is real — I4B's own mechanism
one layer down), nothing stronger is smuggled (the sub-clause is
one-directional). The box's placement argument (a violating chamber puts the
premise out of reach, so the sub-clause must live inside the premise) is
correct. The P3 pairing fix verified against §1.2: φ_q^GMN = Φ_{q−1}^har
(equal degrees, matches the §1.3 perimeter Φ_q = φ_{q+1}); the fixed premise
is the dictionary-correct pairing.

**A.3 The 36+2 census — recomputed exactly.** From the committed
`xi_ledger` with my own is-one test: first-twist census T2A/C/D/G r₀ = 3,
T3A/C/D/E r₀ = 3, T3B/F r₀ = 4, I4B r₀ = 5, I4C r₀ = 3, T2B/E/F + I4A no
twist; 44 junction-levels total (16 r = 2 + 28 r ≥ 3), above-twist = exactly
6 (T3A/T3C/T3D/T3E r = 4, I4C r = 4,5) ⟹ 38 proved-scope ✓. The
instance-warranted set = proved-scope junction-levels whose strictly-below
chain contains an m ≥ 2 junction = proved-scope levels at r ≥ 5 = **exactly
I4A r = 5 and I4B r = 5** (I4B's below-chain r = 4 recorded (1,1) per the
ledger; I4A all-trivial) ⟹ 36 fully derived + 2 instance-warranted ✓. The
36 decompose as 16 r = 2 (TH-BASE, unconditional) + 16 r = 3 (below-chain =
TH-BASE) + 4 r = 4 in proved scope (T3B, T3F, I4A, I4B — below-chain =
TH-BASE + W2-ID1 at the recorded-trivial r = 3) ✓. The grade-cap, §5.2,
§6.1-row, §6.2-row, and §8 wordings of the split all match this computation.

**A.4 The P2 sign revert — verified faithful at source (my own reading of
the print).** Line-exact anchors: tex 1431 `\label{t(i)}` with t_{r−1}(a)_i
= (s_{r−1}(a) − ℓ_{r−1}·v_r(aφ_r^i))/e_{r−1} at tex 1433; u_i = v_r(a_iφ_r^i)
at tex 1373; `\label{rescoeff}` c_i = z_{r−1}^{t_{r−1}(i)}·R_{r−1}(a_i)(z_{r−1})
at tex 1447; the construct child exponent y^{(ℓ_{r−2}u_j−𝔰_j)/e_{r−2}} at tex
1201 with 𝔰_j the initial abscissa of the ideal side T(j). My own shift
computation: s_{r−1}(a) (attained initial abscissa of the polygon, built
from the ℓ-free ordinates u_i) and u_i are ℓ-shift-invariant, so
ℓ ↦ ℓ + k·e gives t ↦ t − k·u_i directly — **the r0 sign, as r2 restores**.
Downstream consistency re-derived: on a side with ordinates u_j = u₀ −
j·h_{r−1}, c_j ↦ z^{−k·u_j}c_j = z^{−k(u₀−jh_{r−1})}c_j, i.e. R^{(ℓ+ke)}(y)
= z^{−ku₀}·R^{(ℓ)}(z^{kh_{r−1}}y) — the unchanged display, with NO k ↦ −k
gloss, exactly as the [r2, P2] bracket says. The §2.3 split is correct: the
note's T = (ℓu − 𝔰)/e is tex 1201's construct exponent (ideal abscissa 𝔰),
the near-negative of Def-t(i)'s (s − ℓu)/e (attained abscissa s); W2-L2's
identity and every use (HR-REC's T_j) are about T itself — machine-keyed
CK-MM 4,396 ✓. The orbit conclusions (ξ ∈ ⟨z_m^{h_m}⟩, coupled
w = z_m^{−kg_mγ_{m+1}}, reachability iff gcd(h_m, ord z_m) | ξ-exponent)
re-checked sign-invariant under k ↦ −k, so nothing downstream moved in
either round — as both brackets state.

**A.5 Anti-re-flip adequacy — CONFIRMED.** The conflation is now
un-repeatable in the practical sense: BOTH print formulas are displayed
byte-true with their tex anchors at BOTH sites (§2.3 and §4.3), the two
opposite sign arrangements are named against each other ("the (s − ℓu)/e
order, the near-negative of T"), and the full failure chain (r0 naming
parenthetical → PE1 F6 computed with the alias → r1 implemented it → PE2
re-derived at source → r2 reverted) is recorded with "Recorded here so no
future round re-flips it". A future flip would have to contradict two
displayed, anchor-pinned source formulas simultaneously. I verified every
quoted formula against the print (A.4); no site still carries the conflated
alias (§2.3's naming line now attributes T to tex 1201 only).

**A.6 The rest of the r2 diff, line-by-line.** S-STATUS: arc facts exact
(083adff 2026-08-06 19:16 / 8d5e3fa 19:45 / 79e796b 2026-08-07 08:20 /
ffa1e57 08:35; counters, finding tallies, next-pass pointers all correct;
19 [r2] bracket sites). Grade-cap [r2, P1] bracket: accurate modulo P1's
"coincides ... PROVED at m = 1" wording. §5.2 warrant rewrite: the struck
text and its replacement state PE2's P1 defect and its cure precisely; the
"NOT definitional" explanation is correct. §6.1 TW-row bracket, §6.2 new
W2-ID1 row + W2-C3/W2-OPEN-2 row brackets, §6.3(d) extension, §6.4 [r2]
block ("open boxes unchanged in count" — correct, OPEN-2a lives inside
W2-OPEN-2): all accurate. §8 round record: matches the PE2 report
clause-by-clause (I compared against 79e796b's text directly). Fold ledger:
WM (M4) + JB row 15 annotations still orchestrator-owed (surfaces verified:
JB line 261 column-(d) face intact; WM (M4) ξ-display face intact under the
[W2]@5463f2a pin); the new WM staleness item is real — "its only commit" is
indeed stale. r2 is note-only: 1 file, +225/−38; runner + probe seals intact.

**A.7 Statement-level truth of the whole note at HEAD.** The r0/r1 core was
CONFIRMED by PE1's full re-derivation (W2-L0–L3, HR-REC, §3.2/§3.4 incl.
linearization error = ξ_Q^δ, W2-C1, transport algebra, T2A reconciliation,
W2-T3E) and PE2's audit; this pass re-verified the r2-touched surfaces
(above), re-derived W2-L2's identity and the §4.3 calculus from source
(A.4), and re-grounded §3.4 + the boundary + the census on a fresh
full-roster leg (§C). Grade-caps, fences, and open boxes are internally
consistent at HEAD; the §4.3 section reads correctly against the print for
the first time in the arc's history. Residual defect: P1 only.

## §B. Machine leg (re-run this pass)

* **Seals:** `grt_w2_checks.py` sha256 `71f8fc90…ba52` — byte-identical
  across working tree, 5463f2a, and HEAD ✓; `grt_weld_probe.py` sha256
  `107c92b6…4ea9` — byte-identical to seal commit 55f7416 ✓.
* **Re-run: exit 0. 6,403 samples, 0 violations, 17 families GREEN, teeth
  MT-TW caught, boundary junctions = 1 (I4B r = 5).** stdout differs from
  the committed output only in three timing figures (0.9/3.1/3.1 vs
  1.0/3.2/3.2 s); results JSON identical except elapsed_s 3.1 vs 3.2 —
  committed bytes restored after the run, `git diff verification/` empty.
  Per-family counts match §6.1 exactly (CK-MM 4,396 · CK-HR1/VD1 156 ·
  CK-REC 55 · CK-SLOT 44/16 · CK-XI 22 · CK-BYTE 28 · TW-RATIO/ADM/STRICT
  44 · TW-F3/F3b 684 · TW-PARI 12 · TW-QO 7 · CK-T3E 2 · MT-TW 2). (The
  runner's 6,403 total = the family sum 6,396 + 6 CK-REC-SKIP + 1
  CK-XI-BOUNDARY record-rows — its own accounting, no note misstatement.)
* **Independent JSON recomputations:** the A.3 census; the 22/22
  equivalence cross-tab + below-r₀ byte-GREEN sweep; I4B ledger
  [(3,(1,1)), (4,(1,1)), (5,(−1,−1))] re-read.

## §C. Fresh leg (route unused by PE1/PE2): the §3.4 display vs the committed ledger at FULL roster scope, modulo the support stabilizer, with my own field arithmetic

PE1 derived the closed form algebraically; PE2 evaluated it at the m = 1
slice (16) plus two hand m = 2 instances. This pass implemented its own
tower-field arithmetic (nested-tuple extensions, own reduce/mul/inv — no
runner imports) and its own §1.1/§3.4 evaluator (Bézout, γ/wΦ recursion,
A_m, χ-chain, (ξ_{m+1}, w_{m+1})), then compared formula vs recorded pair at
EVERY at-or-below-r₀ ledger junction under the correct equivalence — two
pairs satisfy the same orbit equations iff w_f·ξ_f^j = w_r·ξ_r^j on
supp(ψ_m) — with (C-coll) checked per junction. Preregistered predictions
from the note's own claims, all held (`/tmp/w2_pe3_fresh.py`, exit 0):
**22/22 rows**: every non-boundary row consistent AND on (C-coll) —
including the invisible-twist row I4B r = 4 (formula ξ = −1 ≠ 1 yet
consistent with recorded (1,1) on supp {0,2}: rk. 2's stabilizer, exactly)
and the full-support m = 2 rows T3B r = 4 (formula (−1,−1) = ledger) and
T3F r = 4 ((−1,1) = ledger); **I4B r = 5**: (C-coll) FAILS (interior
ξ₃ = −1), formula pair (1,1), NOT consistent with recorded (−1,−1) — the
§3.5 boundary reproduced from scratch. The m = 1 pairs all matched
(z₁^{−e₁A₁}, 1). This also independently re-confirms the F5 renaming
(level-indexed ξ₃ nontrivial, ξ₄ = 1 on I4B) and the c₁ tie. The same
script carries the P1 scan-order probe (§P1).

## §D. Arc accounting — CONSISTENT AND TRUE

Header S-STATUS / §6.4 [r1]+[r2] / §7 / §8 / footer all agree: composed
5463f2a → PE1 083adff (0C+2G+5m) → r1 8d5e3fa (2026-08-06) → PE2 79e796b
(0C+2G+1m) → r2 ffa1e57 (2026-08-07), counter 0/2, repair rounds are not
passes, PE3 = this pass; commit hashes and dates verified against git; open
boxes W2-OPEN-1 + W2-OPEN-2 (now carrying OPEN-2a) + W2-BOX-1 + the §4.3
fence, count unchanged as stated. Runner and artifacts byte-frozen through
both repair rounds ✓. Ungraded observations: (o1) §8's fold item cites "WM
line 88" — WM r5 (f8c2c09, 08:29, six minutes before r2) had already moved
that parenthetical to line 111; the item's content stands (the parenthetical
IS stale) and the pointer rides the "per PE2" attribution — line-drift only.
(o2) The header Genre line still carries r0's "no acceptance arc opened by
this note" parenthetical, superseded loudly by the S-STATUS block one line
below (the parallel §6.4 sentence was already [r1]-struck); stale-but-
harmless under the composition-time reading, seen by two prior passes.
(o3) JA PE4 (535e79f) surfaced JA's own unpinned W-2 consumption — that cure
is billed to JA r3, and no new fold debt accrues to THIS note's ledger.

## Repair queue implied (for the composer; I fix nothing)

R-P1 (one sentence + one flag): scope the four "identification PROVED /
coincidence at m = 1" sites (W2-ID1 Consequently, grade cap [r2, P1], §6.2
W2-C3 row, S-STATUS/§8) to the proved direction, OR pin the §5.1
recorded-pair convention to prefer ξ = 1 (disclosing that the sealed scan's
enumeration order realizes the preference only over prime-field layers —
unobservable on the g ≤ 2 roster); add the converse-direction flag to
W2-OPEN-2's "byte-DIFFERENT for r₀ ≤ q < r" premise clause. No other repair
owed by this pass.

— PE3, GRTW2 acceptance arc, 2026-08-07.
