# HEX3 passPE1 report — hostile verification of HEX3_PROOF_2026-08-08.md

**Pass:** PE1 (first hostile arc on the note that discharged (hExhaust-3)).
**Verifier:** fresh-context Fable, 2026-08-08. **Target:** HEX3_PROOF_2026-08-08.md
at HEAD (seal e3f3459, verdict 671a126; §S8.1 annex applied to W12 at 8e535d2;
HMENU3 landed downstream at 64d3ff9/61ff2f0). **Charges:** (1) THEOREM HEX3.A
re-derived in full (partition, α-scaling, three β-routes, telescoping, R(M)
from W12-L0, ⌊(N−1)/3⌋/small-N off-by-one hunt); (2) conservative-convention
scope vs the w12 instrument; (3) THEOREM HEX3.B bound chain + (A2) conclusion
incl. own re-derivation of conv-decided ⟹ σ-decided; (4) HEX3.C at a
nontrivial route; (5) HEX3-BOX-1 bracket + HMENU3 §S5.4 interaction. Machine
leg: pins, byte-identity, full re-run, count reconciliation. Fresh route: own
enumerator + own law transcription, no runner imports.

**VERDICT: NOT CLEAN — 0 CRITICAL + 2 JUSTIFICATION GAPS + 2 MINOR.** Every
theorem-level claim (HEX3.A law, HEX3.B bounds, HEX3.C, the discharge scope,
the BOX-1 bracket) survived full re-derivation; the machine leg is
bit-reconciled GREEN; the fresh route confirms the law at 9 enumerated rows
(both ring types) and all 46 committed values. The gaps are a false displayed
inequality inside H-2(i)'s justification (conclusion survives with the
corrected pairing, verified here) and a preregistration-bookkeeping
inconsistency in P-1's "eleven never-measured" list.

---

## F1 [JUSTIFICATION GAP] — H-2(i)'s displayed ghost-zone inequality is false at j = 1 (the pairing is backwards); the corrected inequality holds and the conclusion stands

Quote (S3.1, LEMMA H-2(i)):

> Reads: the hull heights at abscissa j are ≤ (3−j)/3·(N−1) (convexity
> from (0, u₀ ≤ N−1) to (3,0)), and (3−j)(N−1)/3 < N−(3−j)k for
> k ≤ (N−1)/3 — so consulted digits sit strictly below the ghost zones
> {≥ N−2k} (B₂), {≥ N−k} (B₁).

The displayed inequality "(3−j)(N−1)/3 < N−(3−j)k" is FALSE at j = 1 for
N ≥ 4 at the k = ⌊(N−1)/3⌋ corner: N = 7, k = 2, j = 1 gives
2·6/3 = 4 < 7 − 4 = 3 — false. (Exactly the corner HEX3-BOX-2(c) told a
hostile pass to attack.) The pairing is backwards: the retained windows under
σ_k are B₂ mod π^{N−2k} (abscissa j = 2, ghost {≥ N−2k}) and B₁ mod π^{N−k}
(abscissa j = 1, ghost {≥ N−k}), so the needed inequality is

    (3−j)(N−1)/3 < N − j·k     (j = 1, 2),

which HOLDS on the whole range k ≤ (N−1)/3: j = 2 ⟺ k < (2N+1)/6 (true,
k ≤ (2N−2)/6); j = 1 ⟺ k < (N+2)/3 (true, k ≤ (N−1)/3). With the corrected
pairing every consulted digit (hull lattice heights ≤ the chord, and the
"point above chord" dichotomy for v(B₁), v(B₂) in the ghost range) sits
strictly below its ghost zone; the shift3-update congruence list in the same
proof (checked separately: B₀′ needs B₁ mod π^{N−k−1}, B₂ mod π^{N−2k−2};
B₁′ mod π^{N−k} needs B₂ mod π^{N−2k−1}; v(s) ≥ k+1 chain-wide via the
three species bounds inside D_k) is correct as displayed. So window
coherence — and with it H-2(ii)/(iii) and the α-term (q−1)q^{3k}u(N−3k) —
survives; the α route is also machine-tied per key at the corner rows
(ALPHA(2) at (2,7)/(2,8)/(2,9), all exact). Classification: justification
gap (false display inside a proof whose conclusion is true and was
re-derived here); repair = replace N−(3−j)k by N−jk.

## F2 [JUSTIFICATION GAP, bookkeeping] — P-1's "ELEVEN never-measured" list contains TWELVE pairs, two of them disclosed as prototype-measured; the honest 11-set omits two listed pairs and includes the unlisted (13,2)

Quote (S7 P-1): "ELEVEN rows are NEW (never measured by any battery):
whole-space values (2,8): 50,176; (2,9): 206,336; (3,5): 23,571; (3,6):
240,327; (4,4): 18,688; (4,5): 308,224; (5,3): 3,125; (5,4): 88,125;
(7,3): 16,807; (9,3): 59,049; (11,3): 161,051; (13,3): 371,293." — that is
12 entries under the label ELEVEN (S10's P-1 line and the runner docstring
repeat the same 12-entry list). Cross-checked against the note's OWN smoke
disclosure (S7 + docstring: prototype rows include Zp (5,3), (7,3)): (5,3)
and (7,3) were measured pre-seal by the /tmp prototype, so they are not
"never measured" in any reading that counts the disclosed prototype. The set
of (q,N) pairs genuinely first-measured by the sealed battery is
{(2,8),(2,9),(3,5),(3,6),(4,4),(4,5),(5,4),(9,3),(11,3),(13,2),(13,3)} —
ELEVEN pairs, matching the header's count and its "incl. N = 9 at q = 2 and
N = 6 at q = 3", but including (13,2) (genuinely never measured; the first
q = 13 row) which the P-1 list omits, and excluding the listed (5,3),(7,3).
Impact: evidential-force bookkeeping only — every listed value did hit
exactly (re-verified here by independent law evaluation), no mathematical
content is touched; but the "11 never-measured pairs" is quoted as "the
battery's force" (S1), so the list should be corrected to the honest set.

## m1 [MINOR] — the S1 anchor u(2,7) = 2¹² + 1504 + 64 decomposes by the FIRST-STEP form's k-terms, directly under the telescoped display

The telescoped sum's k-terms at (2,7) are 1440 (k = 1) and 128 (k = 2);
1504/64 are the first-step recursion's k-terms (8·[u(4)+15·R(4)−2⁶] = 1504,
64·[u(1)+R(1)−1] = 64). Both forms are in the theorem and both sum to 5664
(verified), but the anchor sits immediately under the telescoped display
with no form tag, and a reader checking term-by-term against the displayed
law will get a spurious mismatch. Repair: tag the decomposition
"(first-step form)" or switch to 1440 + 128. (Same paragraph, cosmetic:
S2's (β3) line "left side slope k := t + j... (u₀−t)/2" — content right,
t + j = (u₀−t)/2, typography garbled.)

## m2 [MINOR] — S8.2 item 2's asymptotic gloss drops a (q−1)² factor

The exact N-linear subleading mass of U₃^conv is ⌊(N−4)/2⌋(q−1)²q^{2N−4}
(+ smaller k ≥ 2 terms), so as a joint (N,q)-rate the aside's
"Θ(N·q^{2N−4}) above its head" / "(1 + Θ(N q^{−3}))" understate by
(q−1)² ≈ q²: the true relative rate is ~ N(q−1)²q^{−3}/2 = Θ(N/q),
consistent with the note's OWN rigorous S5.3 bound 1 + N/(2(q+1)). Purely a
downstream aside (explicitly corroboration prose, not a theorem); no
consumer cites it.

---

## Charge-by-charge record (what was re-derived and what checked)

**(1) THEOREM HEX3.A — re-derived IN FULL; law CONFIRMED.**
* *Partition (H-1):* re-derived from first principles. Repeated residual
  roots at n = 3 occur only on e = 1 sides of width ≥ 2 (e ≥ 2 sides carry
  g = 1 residuals; irreducible = separable over a finite field; a repeated
  root of a cubic residual is forced into F_q — degree count kills a
  repeated quadratic factor and char-3 y³−a = (y−a^{1/3})³). Exactly one
  refine per state (width budget 3). The five species + DEC exhaust; every
  locus formula re-derived by slot counts, incl. letter counts (α: q−1;
  β1: (q−1)(q−2), z, z′ ≠ 0 forced by c₀ ≠ 0; β2: z ≠ 0 forced by the
  vertex digit z²; β3: λ, z ≠ 0, the B₀-digit determined). Ranges exact:
  α/β1: 3k ≤ N−1; β2: 3k < u₀ ≤ N−1; β3: u₀ ≡ t (2), u₀ ≥ 3t+2 ⟹ j ≥ 1.
* *α-transport (H-2):* pin cancellation = the (y−z)³ shift identities,
  valid every characteristic (bottom digits of sums/products carry-free);
  z-slice → D_k bijection (injective translate + #slice = #D_k = q^{3N−3−6k}
  + containment); slices are ghost-saturated (pin heights k, 2k, 3k all
  below the ghost thresholds since 3k < N), so drain verdicts transfer at
  fiber q^{3k} = 2k B₂-ghosts + k B₁-ghosts; shear correspondence checked
  (affine-in-j height map, slopes shift by k, residual digits correspond,
  recentering commutes: f(π^k(y+s̃)) = π^{3k}f̃(y+s̃), drain windows exact
  on B₀). D_k drain = q^{3k}u(N−3k). Corner M = 1 consistent (D_k = drain-all
  = q^{3k} = #D_k). FINDING F1 filed against the displayed (i)-inequality.
* *β-routes (H-3):* m-choices verified: β1 split root at exact depth k
  (digit z′−z ≠ 0); β2 pre-depth u₀−2k > k → post-recenter depth exactly k,
  with v(r̃+ẑ) = w = u₀−3k remembered — the u₀-fibers Σ_{w=1}^{M−1}
  (q−1)q^{M−1−w} = q^{M−1}−1 tile the non-degenerate r̃ range exactly
  (degenerate r̃ = −ẑ belongs to no VERT1 key: it needs u₀ ≥ N); β3 split
  root at depth t below the cluster, scaled block enters the depth-j node
  (j = (u₀−3t)/2), node drain q^jR(M−2j) by the n = 2 shear. All three
  target cardinalities re-derived and equal to the slice counts (bijection
  mod q^{3m} ghosts); per-(u₀,k/t) drained forms re-verified against the
  committed JSON with an independent transcription (see fresh route).
  W12-L1(a)(b) consumed at pin as stated.
* *R(M) (H-4):* the sealed w12 block reader's exits inspected in code —
  A₀ = 0 exits are exactly {SPLIT-TAIL, UNDECIDED} (RAM/2SIDED/SPLITEQ/
  INERTDEEP all exit with v(A₀) < window; A₀ = 0 exits at loop top). W-11
  pins re-read: UNDECIDED aggregate q^{M−1} (clause (iii)), SPLIT-TAIL(w)
  per center (q−1)q^{M−2}, w = 1..⌊(M−1)/2⌋ — R(M) = q^{M−1} +
  ⌊(M−1)/2⌋(q−1)q^{M−2} confirmed; the instance bracket Σ(q−1)^t = q^{w−1}
  matches W12-L0's own display. R-recursion R(M) = q^{M−1} +
  (q−1)Σ q^jR(M−2j) verified M ≤ 7 exactly + semantically (n = 2 shear).
  Independent block-level computation of R(3) in char 2 vs odd char:
  different pinned (c₁,c₀) sets, same count q² + (q−1)q both — the HEX3.C
  mechanism observed concretely.
* *Assembly + telescoping (S5):* the k-bracket u(M) + (q^M−1)R(M) − q^{2M−2}
  re-derived exactly ((q−2)q^{M−1}R + (q^{M−1}−1)R + q^{M−1}R = (q^M−1)R);
  the telescoping coefficient of t(N−3l) re-derived: (q−1)q^{3l} +
  (q−1)²q^{4l−1}Σ_{k=1}^{l−1}q^{−k} = (q−1)q^{4l−1}, index bookkeeping
  EXACT (all (k,j) with k+j = l ≤ ⌊(N−1)/3⌋ contribute, no off-by-one);
  q^{2M−2} heads cancel; generating-function form checked
  (1−A = (1−q⁴x³)/(1−q³x³)). Machine: telescoped == first-step over
  9 q × 25 N by independent code (fresh route leg 1). Small-N seeds
  u(1) = 1, u(2) = q², u(3) = q⁴ and the 3k = N−1 corner (empty β2/β3 sums
  self-vanish via the (q^{M−1}−1) and (R(M)−q^{M−1}) factors) all check.

**(2) Convention scope — CONFIRMED.** hex3 `read_fresh` vs sealed w12
`read_trp` read side by side: same hull (None-filtered, same pop rule), same
side/residual extraction, same single-refine detection (read_fresh skips
g = 1 sides — no repeated root possible there), same recentering, and the
SAME unique UNDECIDED exit v(B₀) ≥ N with no tail certification (the
SPLIT-TAIL branch lives in w12's DBL block reader only, not in read_trp).
The w12 battery's committed `U3TRP_measured_conservative` is the whole-space
read_trp-undecided count (code inspected at the cubic-row TRP loop), so
U₃^conv as defined in S1 is exactly what w12 measured; the loop is closed by
XREAD (158,204 pointwise states, 0 divergences — sum re-derived from the
roster by hand: 77,500 Zp + 80,704 Fqt) and W12TIE 23/23. S0's BOX-3 quote
is verbatim against the pinned W12 (diff-checked at e3f3459, whitespace
normalized); "a vanishing U₃^TRP upper bound" as the named obligation is
faithful to the pinned W12's S3.4 ("MISSING: a vanishing U₃^TRP upper
bound — W12-BOX-3") and W-12.D's conditionality display.

**(3) THEOREM HEX3.B — re-derived; CONFIRMED.** conv-decided ⟹ σ-decided
re-derived independently: a conservative-DECIDED chain consults only
in-window digits (chord bound + point-above-chord dichotomy, same mechanism
as H-2(i) corrected), so every disc ≠ 0 lift shares the chain and the final
separable-residual state; Ore pins σ per lift; hence U₃^σ ≤ U₃^conv. Lower
q^N from pinned LEMMA W12-S3.2 (statement re-read). S5.3 re-derived line by
line: R(M) ≤ q^{M−1}(M+1)/2 ⟺ M ≥ 1; k-term ≤ (q−1)(N−2)/2·q^{2N−2}q^{−2k}
(exponent 4k−1+2M−2 = 2N−2k−2 checked); geometric sum gives
u ≤ q^{2N−2}(1+(N−2)/(2(q+1))) ≤ Nq^{2N−2} (N ≥ 2); with W-12.C:
undecided(3,q,N) ≤ (q−1+N)q^{2N−1} ≤ (1+N)q^{2N}, /q^{3N} → 0. Bracket
consistency (Nq^{2N−1} ≤ q^{3N−2} ⟺ N ≤ q^{N−1}) checked. The discharge
claim is convention-free (rides U₃^σ ≤ U₃^conv) and correctly scoped: BOX-4
withholds "W-12.D fires at n = 3"; the (A2) split (σ-undecided part here,
decided-mass absorption = (hMenu-3), DBL boundary tails = W12 r2's own leg,
TRP tail-certified members conv-undecided hence inside this bound) is
exhaustive and matches W12's post-r2 text.

**(4) HEX3.C — re-derived at β2 (and α/char 3, blocks/char 2).** β2 pins
(−2z, z²): odd char injective via −2z; char 2 the pin degenerates to
(0, z²) with z ↦ z² the Frobenius bijection — q−1 pin-pairs either way;
repeated monic quadratics with c₀ ≠ 0 number q−1 in EVERY characteristic
(disc c₁² − 4c₀: odd char c₁ ≠ 0 forced, char 2 c₁ = 0 forced). α/char 3:
(y−z)³ = y³ − z³, cube map bijective, q−1 pinned triples. Transports are
digit bijections in both ring types; coherence is a quotient-hom statement.
The R(3) two-characteristic computation (above) shows the count-preservation
concretely. CHAR 17/17 at tally granularity confirms. The corollary claims
only U₃^conv; U₃^σ char-independence correctly left open (BOX-1).

**(5) BOX-1 + HMENU3 §S5.4 — CONSISTENT, no overclaim found.** BOX-1's
bracket q^N ≤ U₃^σ ≤ U₃^conv = q·u matches A/B; its mechanism display
(R = q^{M−1} hidden + ⌊(M−1)/2⌋(q−1)q^{M−2} block-certifiable SPLIT-TAIL)
matches the W-11 rows. HMENU3 §S5.4 parks the σ-nuance off-critical-path via
(A2)'s definition (residue is σ-unlabeled; (A0) core-only) — nothing in
HEX3's text depends on that placement or anticipates more: the exact law is
everywhere conv-scoped, the discharge everywhere σ-side-bounded, and S8.2
merely offers the machinery to W-13. The §S8.1 annex as applied at 8e535d2
is byte-identical (md5 of lines 516–527 = 1345d5eff57114c00c98fb2d600a3676,
matching the ledger pin); the W12 wrapper's r2-corrected qualifier placement
(discharge convention-free, law conv-scoped) agrees with HEX3.B.

## Machine leg (this pass)

* PINS: all four md5 pins re-hashed and MATCH (w12_checks.py 7dc0…,
  w11_checks.py 500a…, w10_checks.py a9c3…, w12 JSON 0577…).
* Runner byte-identical to seal e3f3459 (git diff empty; md5 83faf7ed…).
* FULL RE-RUN (single fresh run, this machine): exit 0, GREEN, 327.3 s.
  158,512 checks / 0 violations: PIN 4, LAW 92, SPECIES 172, XREAD 158,204,
  W12TIE 23, CHAR 17 — every count equal to §S10's. Teeth fired 10/20/13 ==
  preregistered; fire-row sets re-derived from the roster by hand (T-FLOOR:
  N ∈ {5,7,8,9} rows = 10; T-ALPHA: N ≥ 4 rows = 20; T-VERT1: N ≥ 5 rows
  = 13). 46/46 rows, 67,410,225 states (JSON-summed). Artifacts
  content-identical to the committed ones except timing fields; committed
  artifacts restored after comparison.

## Fresh route (no runner imports; /tmp/hex3_fresh_verify.py)

Independent implementations: own Zp/Fqt digit arithmetic, own lower hull
(min-slope walk, different algorithm), own residual multiplicity (deflation),
own recentering (generic 4-coefficient Taylor shift, not shift3), own law
transcription from the theorem display. Results:
* leg 1: telescoped form == first-step recursion, 9 q-values × N ≤ 25, 0
  mismatches.
* leg 2: own law vs committed u_measured — 46/46 rows equal.
* leg 3: own law at big rows == preregistered whole-space values: (2,9)
  206,336; (3,6) 240,327; (4,5) 308,224; (13,3) 371,293; (2,8) 50,176.
* leg 4: own ENUMERATION == law at 9 rows, both ring types: Zp (2,4) 72,
  (3,4) 837, (5,3) 625, (2,5) 304, (2,6) 1360; Fqt (3,4) 837, (2,5) 304,
  (2,7) 5664, (3,5) 7857.
* per-key: own species-table transcription vs committed JSON species_tally
  on 6 rows incl. (Zp,2,9), (Zp,3,6), (Fqt,4,5), (Zp,13,3): all keys, both
  directions, partition sums, DECIDED-drains-0 — all exact.

## Disposition

0 CRITICAL. The theorems stand as composed. Repair owed on F1 (one-line
inequality fix in H-2(i)), F2 (correct the P-1/S10/docstring list to the
honest 11-set or relabel), m1/m2 (cosmetic). Counter stays per protocol;
this pass = PE1, findings trigger repair, 2-clean accepts.
