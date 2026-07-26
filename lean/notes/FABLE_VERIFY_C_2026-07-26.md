# FABLE fresh-instance verification of §C (MOVES_2026-07-24.md, live text from '## §C REV 2')

Verifier: Fable (fresh instance, decorrelated from Codex passes 1–13).
Date: 2026-07-26. Method: quote verbatim; CRITICAL ERROR vs JUSTIFICATION GAP;
fix nothing. Mandatory checks: (1) independent (ZC) re-derivation through one
increment + one recentering; (2) a NEW joint history (not in any record)
pushed through the mass recursion numerically; (3) DOM/TYP/LST audited as if
unproven. Pass records read only AFTER sections 1–4 were drafted.

## 0. Reading order followed

§B2-DEF (D.0–D.12) → C10B_DERIVATION → C15_DERIVATION → live §C (C.0–C.3)
→ my own checks → pass records 2–13 (record↔text consistency).

## 1. Independent re-derivation of the (ZC) induction

Done by hand for one increment (root recentering -> non-adjacent (1,3,2)
increment) and one recentering (D.10 g=1), tracking Z/DIG/mass. Steps that
CHECK OUT independently: strip zeros are free coordinates of the solved
graph even when they appear as non-lead arguments of DIG (the (ZC-b')
amendment is genuinely what the count needs); the fresh value digit is a
function of the weight-gamma' level set alone on the joint zero locus
(TYP(a)'s display is right: class map additive, kills weight > delta');
equal-fiber counting via additivity is sound; persistence STEP A/B sound
GIVEN hull-consistent node data; kappa bookkeeping (LST) verified
concretely: w1(Phi1) = h1 at the read that augments Phi1, so
kappa_{Phi1} = h1/(e1 STR1) — consistent, no stale-kappa issue.
The induction FAILS only where noted in Finding 1 below (data admitted by
C.0's realizability for which the E_inh-implication premise is false).

FINDING 1 — CRITICAL. Location: C.0 REALIZABLE histories (lines ~3183-3195)
+ Lemma DOM step (2) (~3304) + C.1(i) alpha-chain (~3506) + Theorem C.
Quote (C.0): "its data satisfy the two side conditions ... (NA) ... (HV)".
Quote (DOM(2)): "VERTEX-ENTRY INEQUALITY [source: D.8's box]".
Defect: (NA)+(HV) is NOT a complete realizability list. For a NON-ADJACENT
read the strict span-entry inequality new(j) > old(j) at span slots
j < mu_i (equivalently new(j*) > old(j*)) is an independent data condition:
nothing in (I-aug)+(NA)+(HV) implies it. Explicit data counterexample
(worked in sec. 2's script, config F-EMPTY): window mu_0 = 3, old(j) = 3-j
(root recentering, w(Phi1) = 1); read side [0,2], e1 = 1, h1 = 3,
new = (7,4,1,-2). I-aug: 3 > 1 OK; (NA): new(3) = -2 < 0 = old(3) OK; (HV)
vacuous. But new(2) = 1 = old(2): the endpoint value digit sits AT the
floor, is classed E_inh by C.1's selection ("heights ... STRICTLY ABOVE
F_i"), and C.1(i)'s claim that E_inh is implied on Sigma_i is FALSE for it
(a nonzero-digit demand at a coordinate zero-pinned by (BOX)): the joint
stratum is EMPTY while vol_nom(E_fresh) = 2^{-6} > 0. Hence C.1.5(1) and
Theorem C(b) are false as quantified (positive predicted mass, empty
locus), and Theorem C(a) fails too (S(H,Z) = empty != locus(T(H,Z))).
Root cause: DOM's proof derives new(j*) >= old(j*) from "D.8's box" — an
f-statement valid only on a nonempty stratum — inside a lemma quantified
over realizable (data-only) prefixes: circular for empty strata. DOM's
STATEMENT itself is false for such data (variant new(0) = 2 < old(0) = 3:
line_1(0) < line_0(0) on the interior). C10B S3.3 spotted the (gamma)-side
data condition (became (NA)) but missed the span-entry twin; S6.2's
"REJECTED h2=28 read" is exactly this phenomenon one frame up — the
derivation EXCLUDED it by hand ("non-hull read") without adding the
exclusion to C.0's predicate. Repair shape (not applied): add to C.0 a
third data condition (SAE): new(j) > old(j) for span slots j < mu_i and
new(s0'+w') = old(mu_i) - (mu_i - s0'-w')·w(Phi-hat_i) ... i.e. side line
strictly above the box line on [0, mu_i) and weakly at mu_i; then DOM(2)
cites (SAE), not D.8. All sealed censuses used hull-consistent data, so
no census could catch this.

FINDING 2 — JUSTIFICATION GAP. Location: C.0 histories (~3153-3157).
Quote: "each ν_i carries its species and data as in rev 1".
Defect: rev 1's body is excised ("## §C rev 1 — SUPERSEDED; body excised");
the live text nowhere defines the node datum tuple (which of e, h, g, psi,
mu, anchor a, pattern digits, s0', side height are data). Every C.0
predicate ((†)-anchors, vtx, R_anch) and Finding 1's adjudication depend on
this parametrization. A self-contained §C needs the tuple displayed.

## 2. New numerical joint history (mass recursion)

Script /tmp/fable_c_check.py (4x10^6 members). History NOT in any record
(no non-adjacent read was ever censused; C15 S5 covers adjacent chains,
Case-L covers s0'>0 recentering): n=4, p=2; node0 = root recentering read
(key x, side [0,3] slope 1, psi0 = z+1, mu0 = 3, Phi1 = x+2); node1 =
NON-ADJACENT increment, side [0,2], (e1,h1) = (1,3), new = (8,5,2,-1) vs
old = (3,2,1,0), (NA) active (-1 < 0), residual psi1 = z^2+z+1 (mu1 = 1,
g1 = 2, F4), m* = 9; node2 = adjacent tail read, Phi2 = x^2+12x+84,
h2 = 7 > 6 = w1(Phi2), fresh F4-digit level set {(0,9),(1,6)}, m* = 2.
RESULTS: sanity 0/4M; P(n1|n0) = 0.001975 vs 2^-9 = 0.001953 (z = +0.98);
P(n2|n1) = 0.24902 vs 1/4 (z = -0.20); joint 4.917e-4 vs 4.883e-4;
inherited-floor + vertex-transport falsifier (v(c00)>=9, v(c01)>=6,
v(c10)=2, dig = vtx(nu1) = 1): 0 violations of 7899. So the (ZC) engine is
EXACT on hull-consistent data including the uncensused non-adjacent
species — C.1.5's mechanism confirmed at a fresh census point.
F-EMPTY demonstrator (Finding 1): the read (e1,h1) = (1,3), new =
(7,4,1,-2) passes (I-aug)+(NA)+(HV); C.1 selection gives m* = 6 (endpoint
digit at floor -> E_inh). Theorem C(b) predicts 2^-6 x 4M = 62500 members;
locus of the fresh-only system T(H) = 62478 (nominal arithmetic OK); TRUE
joint stratum = 0. Theorem C(a) and (b) both fail on this C.0-realizable
history. Finding 1 is numerically certified, not hypothetical.

## 3. Audit of Lemmas DOM / TYP / LST as if unproven

DOM: (1) affine-difference + I-aug slope: sound. (2) entry inequality:
sourced from "D.8's box" = f-content — Finding 1 (CRITICAL, shared root
cause); statement itself false for entry-violating realizable-per-C.0
prefixes (new(0) = 2 variant). (3) width confinement: sound (psi^mu |
residual). (PU): intercept argument w'(f) = e'.new(0) needs every slot
weakly above the new line — window slots via the STRATUM's clauses (again
f-content, same caveat), transport slots via K1 + (2): sound given (SAE).
FLOOR FORM step (nested blocks, left-edge convention, lines descend):
checked line by line — sound. Base i = 0 (cluster absorbed): sound.
VERDICT: correct exactly on the (SAE)-augmented quantifier; no second
independent defect found.
LST: (i) ht = K1-chain weight: verified concretely (sec. 2 history):
w1(Phi1) = h1 = 3 at the augmenting read, kappa = h/(e.STR) — the
per-key update discipline is right; recentering case (key replaced,
no inner level) sound. (ii) reduces to DOM (Finding-1-conditional).
(iii) block-constancy of the floor in ht: sound given (ii).
VERDICT: no independent defect; inherits Finding 1 through (ii).
TYP: (a) display in_{gamma'}(B) = sum over level set — checked: class
map additive, kills weight > delta', unit lifts reduce to F_p-scalars on
each base digit; CONSEQUENCE (piece = additive span of monomial classes)
follows since every piece element is [B] with the display unconditional.
(b) equal-fiber count for an additive surjection: sound; the alphabet =
image convention matches D.11 (checked against sec. 2's 1-dim piece
{(2,2)}: alphabet F_2 inside F_4 — exercised by the vertex falsifier).
(c) scope statement: sound. VERDICT: TYP clean as stated.

FINDING 3 — JUSTIFICATION GAP (display). Location: C.1.5 proof of (2)
(~3663). Quote: "old zeros beyond the crossing slot (indices >=
j.D_{i+1} > w'D_{i+1})". The strict inequality fails in the adjacent
s0' = 0 case (j-cross = mu_i = w'): then j.D = w'D exactly. Conclusion
survives (survivor indices >= mu_i D_{i+1} >= mu_{i+1} D_{i+2} by (N1)),
but the displayed chain is wrong as written at that boundary case.

FINDING 4 — JUSTIFICATION GAP (wording). Location: C.2 ADMISSIBLE Z
(~3680). Quote: "SOLVES FOR coordinates lying in the free-coordinate
complement of Sigma_k's locus". As parsed, "free-coordinate complement" =
the complement of the free coordinates = the DETERMINED set — the
opposite of the intent (the next sentence and C15 S6 make the intent
clear: pins of Z must be FREE on Sigma_k). One-word ambiguity in a
load-bearing definition.

## 4. Line-audit findings on C.0 / C.0.5 / C.1 / C.1.5 / C.2 / C.3

(Line refs: the file grew +280 lines mid-verification — see sec. 5; new
numbering: §C REV 2 at 3398, C.0 realizability ~3466, DOM ~3561, C.1(i)
~3769, C.1.5 ~3885, C.2 ~3957.)

FINDING 5 — JUSTIFICATION GAP (display; formally an inconsistency).
Location: (ZC-a), both in C.1.5 (~3906) and C.1's floor citation.
Quote: "Z_i := the literal zero downset with per-index top F_i := the
pointwise max of the history's line staircases over their clause regions".
Defect: read literally, node m's staircase at its own vertex/rim blocks
tops AT the line level old_m(mu_m) — but DIG_i pins NONZERO values at
exactly those (b, ht = old_m) level sets; Z_i union DIG_i would then be
contradictory and every Sigma_i empty. The intended downset (per the C10B
S2.1 dual "vanishing resp. digit demands" reading, the initialization
"Z_0 = cluster zeros + (BOX)", and both instance scripts) stops strictly
below the line at value-carrying rim slots. Consumers are interior-only
(where (BOX)-strict makes inclusive tops correct), so no downstream
damage, but the displayed formula does not say what the proof uses.

Checked and CLEAN (no finding): C.0.5 unitriangularity + PIN-WELLDEF
scope; the block convention; vtx well-definedness (consistency of C.0's
vtx with D.8's (VERTEX) display verified by hand: R(f) = z^a R_anch);
C.1's species selection self-consistency on hull-consistent data; strip
freeness under (ZC-b') non-lead occurrences; TYP(a/b/c) in full; value
level-set disjointness; the adjacent-hinge degeneration to (HV); C.2's
N(H,Z) finiteness; C.3's cardinality-only volume language; root-move
inclusion in Psi_H; lift-translation scope clause vs D.10's scope.

## 5. Record <-> text consistency (read after secs 1-4 were drafted)

- Repair lineage (passes 2-13) matches the live text: every claimed purge
  (full-window domination, "windows NEST", stride-address caveat, Lambda_fresh,
  rev-8 pin-count bracket) is really gone; DOM/TYP/LST match the rev-10/11
  records; Case-L record numbers match C.3's citation.
- Finding 1 is INVISIBLE to the pass-record method: every pass audited
  implication/counting on strata, never completeness of the realizability
  predicate against empty-stratum data. Pass-6 gap 4 introduced (NA)/(HV)
  as "the two data-side conditions" from the (gamma)/hinge analysis only;
  the span-entry twin was consumed silently via witness reasoning in C10B
  S3.3 ("the endpoint is a hull vertex strictly above the old line by
  BOX") — an inherited defect from the (earlier Fable) C10B derivation,
  which Codex then audited only for internal soundness. S6.2's rejected
  h2=28 read was the phenomenon surfacing live; it was excluded BY HAND
  ("non-hull read") without the exclusion entering C.0.
- CAVEAT: MOVES_2026-07-24.md changed during this verification (4162 ->
  5223 lines; commits 55e0698..cc8123d): the live §C text is byte-identical
  (shift +280) — verified by spot-checks — but §B2-DEF underwent a
  concurrent D11..D11d repair spiral. This §C verdict is against the
  §B2-DEF interfaces as I read them (pre-D11); records claim the D11
  spiral is B2-internal (counting bridge, attainable blocks). If any D11
  repair touched D.3(e)/D.8/D.11 statements, §C's citations need a re-scan.

## 6. Verdict

Counts: 1 CRITICAL (Finding 1), 4 JUSTIFICATION GAPS (Findings 2-5).
The counting ENGINE ((ZC), DOM-on-hull-consistent-data, TYP, LST, C.1.5's
conditional exactness, Theorem C's product) is sound and was confirmed
exactly at a fresh, never-censused non-adjacent 3-node history
(sec. 2: z <= 1.0 on all three conditionals; falsifiers 0). The defect is
at the QUANTIFIER: C.0's realizability predicate ((NA)+(HV)) is
incomplete; §C as stated asserts positive mass for data-realizable
histories with empty strata (numerically certified: predicted 62500,
true 0). Repair is local (a third data condition (SAE): the read side
strictly above the old box line on span slots < mu_i — plus its adjacent
height-match analogue new(mu_i) = old(mu_i) if the node parametrization
does not force it), after which DOM's (2) cites (SAE) and every proof I
audited goes through unchanged.
VERDICT: NOT CLEAN (1 critical, 4 gaps).

## 5. Record ↔ text consistency (read last)

(status: pending)

## 6. Verdict

(status: pending)
