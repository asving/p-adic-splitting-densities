# GRTJB passPE10 report — hostile verification pass (THE ACCEPTANCE PASS; eighth acceptance attempt)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` at HEAD (commit
`49f9168` = r8, THE ONE-QUOTATION ROUND; verified unchanged at HEAD
`52d40bb` — `git diff 49f9168 HEAD -- <note>` is empty). **Reader:**
fresh-context hostile verifier; fixes nothing; quote-and-classify.
**Inputs read:** the full note at HEAD (3,101 lines, top to bottom), all
NINE prior pass reports (PE1 `85a8dc9` … PE9 `b0b4c3a`) including their
exhaustive re-derivation-route disclosures, the four sealed instruments +
committed artifacts in `verification/openmath/`, and the consumed-source
slices cited below ([RMG] `RMENGINE_2026-08-08.md`, J-A
`GRTJA_PROOF_2026-08-08.md`, the O1thr rev-3 brief, `grt_weld_probe`
artifacts). **Acceptance rule:** PE9 was CLEAN, so the counter stands 1/2
entering this pass; a clean pass here is the second consecutive clean —
the acceptance/ledger action is the orchestrator's, not this report's.

---

## §0. VERDICT

**0 CRITICAL ERRORS, 0 JUSTIFICATION GAPS, 0 minor — CLEAN.**

Second consecutive clean pass (eighth acceptance attempt). Machine legs
4/4 bit-exact at HEAD (§1). Both charged fresh-route re-derivations
CONFIRM their components (§2–§3). Statement-level truth of the whole note
at HEAD: no defect found (§4). Arc accounting consistent and true (§5).
PE9's three unscored observations adjudicated — all three stand as
non-findings (§6). Three unscored observations of my own (§7).

---

## §1. MACHINE LEG — all four instruments at HEAD

All four md5s checked at their sealed values BEFORE and AFTER the runs;
all four scripts re-run from the committed tree; every stdout diffed
0-line against its committed output (elapsed values reproduced); every
rewritten JSON byte-identical to the committed artifact
(`git status`/`git diff -- verification/` empty after the reruns):

| instrument | md5 (sealed value, intact) | exit | stdout vs committed |
|---|---|---|---|
| `grt_jb_checks.py` | `55f4911eaddd8524fd91368b30ed71bd` | 0 | 0-line diff |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` | 0 | 0-line diff |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` | 0 | 0-line diff |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` | 0 | 0-line diff |

**Figures vs the note — exact**, read from the fresh stdouts: 6,700
samples, 18/18 families GREEN, 0 violations, teeth CAUGHT; JB-DEV/JB-SHEAR/
JB-VTX 893 each, JB-KEYEQ 25, JB-ID 34, JB-TREE 79, JB-LINE 194, JB-EPS
955, JB-CM 28, JB-CREAD 79, JB-QO 5 / JB-D0 4, TW-JB 2,480, teeth 3/3/3/3;
censuses scored 104 / boundary 21 / v=0 0 / R=0 0 / off-perimeter 0;
walker 458 total = 362 law + 96 counters, leg-A 84 walks (12 at
byte-unequal junctions), PW-XFRAME 72; walker2 45/45 + 27 + 28 = 100 law
samples GREEN; level census 45/8/3 scored, 0/10/3 boundary, 13 + 8 = 21
cross-check, 0 scope-outs.

**Independent recomputations from the sealed JSON (my own scripts, not
the runners' printouts):** JB-CREAD scored decomposition **104 = roster 56
+ QO 2 + d₀ 8 + chamber 38** (G2-7's display, recounted); boundary **21**;
teeth material **22 samples over 21 teeth-positive rows over exactly the
14 towers** the r1/G-2 bracket lists (name-for-name match); tree walks
**79 base / 125 with chambers**; **EIGHT `byteeq: false` tree rows** = 4
base (T3A/T3C/T3D/T3E at m=2, 3 walks each) + 4 chamber `/tw` (2 walks
each, unreached) — exactly G2-3; byte census **22 rows q=1 true + 3
vacuous empty-census rows** (`QO:x3-3/Q3`, `QO:x4+2x2+2/Q2`,
`QO:x4-2/Q2`) — exactly r1/G-3; the walker's 9 `chain_eq ∧ chat_eq`
degenerate rows re-read from the fresh stdout match the G2-2 list
row-for-row; the weld probe's committed output shows F1 = 18 RED of 30
walked, i.e. **12 GREEN / 18 RED** — §2(ii)'s quoted figure exact.
**The r4/F-3 5-vs-11 split re-derived from the census data alone:** the
towers with a `false` census entry below their top are exactly
T3A/T3C/T3D/T3E (shared_upto = 1 < n = 2) and I4C (shared_upto = 1 <
n = 3, qcap = 2); every other roster tower has its full walked chain
`true` (T2A–T2G at n = 1; T3B/T3F at n = 2; I4A/I4B at n = 3), giving
qcap = n ≤ shared_upto — the two fences coincide there, exactly as §0M
column (a2) states.

---

## §2. CHARGE — fresh-route re-derivation 1: the §5 four-line u ≥ 0
theorem by the CONE-DECOMPOSITION route

**Component:** §5's [r5, F-3] display — u := (V − s_m^wt(V)·h_{m−1})/e_{m−1}
≥ 0 for every V ∈ 𝒲_m — the discharge theorem behind §0M rows 4/12's
narrowed column (b).

**Every prior route (disclosed lists checked):** the note's own steps
(1)–(4) (divisibility of E_m and Γ_{l≤m−2} by e_{m−1}; the congruence
V ≡ j_{m−1}h_{m−1}; an inequality chain discarding terms and using
γ_m ≥ h_{m−1}); PE5 re-derived those steps from the displayed description;
PE6 re-derived them and enumerated 598,500 members; PE8 re-derived the
m = 1 case from scratch (same steps); PE9 re-checked steps (1)–(4). PE7's
j := s decomposition is the CONVERSE direction at m = 1 only
({u ≥ 0} ⊆ 𝒲₁). No report and not the note derived u ≥ 0 by cone
membership.

**My route (new): exact regrouping into the (e, h)-cone, then a
standalone cone lemma.** Write e := e_{m−1}, h := h_{m−1},
𝒞 := {e·A + h·j : A, j ∈ ℤ_{≥0}}.

1. **(REGROUP) 𝒲_m ⊆ 𝒞, with an EXACT decomposition.** From the [RMG]
   S2.1 constants (verified at source, RMENGINE L297–299: E_m = e₀⋯e_{m−1},
   Γ_l = γ_{l+1}·∏_{l<t<m} e_t, Γ_{m−1} = γ_m): E_m = e·E_{m−1}; for
   l ≤ m−2 the product contains t = m−1, so Γ_l = e·Γ_l^{(m−1)} with
   Γ_l^{(m−1)} the level-(m−1) constant (the same factor-out RMENGINE
   itself uses at its L582–583); and γ_m = e·W + h with
   W := w_{m−1}Φ_{m−1} ≥ 0 (W = 0 at m = 1). Hence every lattice member
   V = E_m·a + Σ_{l<m} j_l·Γ_l regroups EXACTLY as

       V = e·A + h·j,   A := E_{m−1}·a + Σ_{l≤m−2} j_l·Γ_l^{(m−1)} + j_{m−1}·W ≥ 0,
                        j := j_{m−1} ≥ 0.

2. **(CONE LEMMA) u ≥ 0 on ALL of 𝒞.** For V = e·A + h·j with A, j ≥ 0:
   ℓV ≡ ℓhj ≡ j (mod e), so s(V) = j mod e ≤ j and e | (j − s(V)); then
   V − s(V)·h = e·A + (j − s(V))·h gives the EXACT nonnegative
   decomposition u(V) = A + ((j − s(V))/e)·h ≥ 0. ∎

**How this differs from every used route:** no congruence-on-V step and
no inequality chain — the note's steps (2)+(3) are replaced by one exact
regrouping and one exact decomposition of u itself (nothing is discarded,
γ_m ≥ h is never invoked); and it proves the STRONGER statement u ≥ 0 on
the whole cone 𝒞 ⊇ 𝒲_m (the j_l ≤ P_l − 1 caps are never used). Shared
ingredient, disclosed: the divisibility structure of the constants is the
same fact the note's step (1) records — unavoidable, since the constants
are what they are; the argument built on it is different. **Corollaries
re-obtained:** J-A's (e, h) = (2, 3), V = 1 instance is excluded from the
whole cone (2A + 3j = 1 insoluble in ℤ_{≥0}²), a fortiori from 𝒲₁ — the
§5 parity corollary strengthened; and combining my (⊇) with PE7's j := s
decomposition — which generalizes verbatim to every m — gives the exact
identity **{V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒞 at EVERY m** (see Observation
§7(b)). The note's §5 display, its narrowed column-(b) status at rows
4/12, and the m = 1 equivalence all CONFIRM under this route.

**Fresh machine leg (my own implementation; no runner code, no JSON
reuse; read-only, /tmp):** cone lemma exhaustive over e ≤ 8, h ≤ 10
coprime, A, j ∈ [0, 15) — 46,800 checks; lattice regrouping on 1-level
chains exhaustive (all coprime (e₀, h₀) with e₀ ≤ 6, h₀ ≤ 8, g₀ ≤ 3) plus
400 random 2-/3-level read chains (W_l ∈ [0, 2], W₀ = 0), verifying the
exact regrouping identity V = e·A + h·j, A ≥ 0, s(V) = j mod e, and
u ≥ 0 per member — 279,405 checks; the (2,3)-exclusion instance.
**Total 326,206 checks, 0 violations.**

---

## §3. CHARGE — fresh-route re-derivation 2: JB-VTX(b)/(c) by the
SUPPORT-FUNCTION (argmin-duality) route

**Component:** §3's clauses (b) (vertex-for-vertex through the shear) and
(c) (slope/length translation, realized side ↦ horizontal), given clause
(a)'s pointwise shear — the same conditional structure as the note, which
derives (b) from (a) + LEMMA JB-AFF and (c) by substitution arithmetic.

**Every prior route:** the note (JB-AFF's chord-order argument: affine
abscissa-preserving maps with a > 0 preserve "lies strictly below the
chord"); PE1 re-derived the shear + slope law directly; PE3 re-derived
(b)/(c) and JB-AFF from the print source; PE9 re-checked (b) via JB-AFF
and (c) by substitution. No report used a duality/support-function
argument.

**My route (new): the lower hull read off the argmin structure of the
slope-parameterized support function.** For a finite set
S = {(i, u_i)} with distinct abscissas (U(f) is one point per digit — a
graph), define G_S(t) := min_i (u_i − t·i) and M_S(t) := the argmin set.
The duality dictionary (derived, then machine-cross-validated against the
raw supporting-line definition): (i, u_i) is a lower-hull VERTEX iff
M_S(t) = {i} for some t; the hull has an EDGE of slope t iff |M_S(t)| ≥ 2,
with abscissa extent [min M_S(t), max M_S(t)]. Under the shear
Σ : (i, u) ↦ (i, e·u + h·i) with e ≥ 1:

    G_{Σ(S)}(t) = min_i (e·u_i + (h − t)·i) = e·G_S((t − h)/e),
    M_{Σ(S)}(t) = M_S((t − h)/e)   — as INDEX SETS, exactly.

Since t ↦ (t − h)/e is an increasing bijection of ℝ: unique-argmin
parameters correspond, so the vertex sets of S and Σ(S) are EQUAL as
abscissa sets — JB-VTX(b), vertex-for-vertex, same abscissas; and the
edge at print slope σ is the edge at sheared slope e·σ + h with the SAME
argmin set — the slope law of (c), lengths (abscissa runs) preserved
because the argmin sets are literally equal; the realized side
σ = −h/e ↦ slope 0 (horizontal), and the sheared min ordinate is
G_{Σ(S)}(0) = e·G_S(−h/e) — the eq-(12) presentation, consistent with
(d)'s reading (not claimed here; (d) consumes JA-VAL). This route never
constructs a hull, never compares chords, and never invokes JB-AFF; it
subsumes JB-AFF's content for these maps as the one-line transformation
law of G_S.

**Fresh machine leg (own code, exact rational arithmetic):** 3,000 random
point sets (2–9 points, abscissas ⊂ [0, 12], ordinates ∈ [−20, 20]),
shears with e ∈ [1, 5], h ∈ [−4, 7] (JB-AFF's full generality, not just
the tower's h ≥ 1): verified (b) vertex-set equality, the argmin
dictionary M_{Σ(S)}(e·t + h) = M_S(t) at every pairwise-slope breakpoint
AND at off-breakpoint probes, the slope/length law edge-for-edge, and —
the decorrelation leg — my duality-computed vertex set against an
independent O(n³) supporting-line-definition checker (the JB-AFF-side
characterization), agreeing on all 3,000 instances. **106,562 checks, 0
violations.** (Combined probe total §2+§3: 432,768 checks, 0 violations;
no repository file touched.)

---

## §4. CHARGE — statement-level truth of the whole note at HEAD

**The four theorem boxes, fences read as part of the statements:**
JB-DEV/JB-VTX/JB-TREE/JB-CREAD each **TRUE AS FENCED** — the five-line
JB-CREAD chain re-verified once more (ninth reading: (VD-m) at f; the
L-CELL(ii) on-line cell from v·τ_m ≠ 0; the (C-W_R) pin; (C-READ); the
JB-EPS collapse with ε′ verbatim against the quoted (RM-m) box); JB-EPS's
telescope re-checked (and independently underwritten by §2's cone lemma,
which yields s(V)+s(V′)−s(V+V′) = e·ε′ on the cone); §3(a)'s shear
arithmetic re-checked against JA-PIN clause 7; §4(ii)'s digit-list degree
bound re-checked (e_i·k < P_i for k < g_i; deg C_k Φ_i^{e_i k} < deg
Φ_{i+1}).

**Matrix-surface cross-checks at rows COMPLEMENTARY to PE9's list** (PE9
did 3/4/5/11/12/19/20/21/22): rows 1, 2, 6, 13, 15, 17, 18, 23 checked
cell-for-cell against surfaces 2 (§2 ∎), 3 (§3 ∎), 4 (§4 ∎), the §7.2
rows and surface 14 — consistent everywhere; row 24's four record cells
match surface 14's enumeration and summary points (2)/(4) exactly ((a1):
3,4,8–13,17,18; (a2): 2, 5, 11(d3); (b): 4, 12; (c): 18, 21, 22, 23).
**Independent frontier re-walk over all 28 rows** under the criterion's
own words (open proviso + NO leg): rows 4, 5, 12, 22 and NO OTHER — rows
13/18/20 excluded for exactly the displayed reasons (consumption at
grade, not an open proviso; row 20's (c) is row 21's context inherited);
rows 15/17's no-leg sub-cells (chamber walks; LED-Λ attempt) carry scope
fences and grade rides, not open provisos. **THE CENSUS IS FOUR — the
note's figure.**

**Code-transcription claims re-read from committed source (all exact):**
`grt_jb_checks.py` L283 is byte-for-byte `if q + 1 <= G.RANK and minH !=
G.vgen(q + 2, f):` under `if q <= L:` with `L = GJA.shared_upto(T, G)`
(⟨n3⟩/m-3); `qcap_of(T,G) = min(T.n, GJA.shared_upto(T,G) + 1)` at L210
(§1's display); `GmnLeg.__init__` sets `self.RANK = len(levels)` and
`gmn_from_tower` passes `range(T.NR)` levels, so RANK = n+1 ≥ qcap+1 (the
redundancy re-derivation); `jb_eps` samples `range(0, min(3*e*h + 5,
25))` stepped `[::2]`/`[::3]` (row 20's r4/F-5 cell, exact); ⟨n1⟩'s
SAME-COMPUTATION mechanism confirmed (`self.P = ITL.PolyO(R)` on the
tower's own ring; third leg guarded by `tuple(G.phi[q+1]) == key` after
the `continue` on `dvF != dvI`); the r1 walker's PW-XFRAME gate is
`chain_eq` alone (L374–376 region as cited); TH-BASE's guard
`if T.n >= 1 and not cen.get(1, True)` is unexercised exactly on the 3
empty-census rows.

**Quotation and source pins:** the r8 bracket's fusion analysis
byte-verified myself (wrap-normalized): site A's string occurs 3× (the
col-(b) strike site, the r8 bracket quote, and as the fused string's
prefix), site B's 2× (the §5 strike site, the r8 bracket quote), the
fused string exactly 1× (struck) and is programmatically site A + " (or
weaker one)"; grep-swept: NO live unstruck "not an equivalent" or
necessity-"exactly" assertion survives (the r6 round block's instance is
a dated record carrying its [r7, F-1] annotation in place). [RMG] pins:
E_m/Γ_l at RMENGINE L297–299, P_l := e_l·g_l "local to this note" at
L296, line(C) display at L413 — verbatim as consumed. J-A pins: the
level-indexed perimeter sentence and the "PROVED unconditionally on the
shared-key perimeter" grade, both present at source. The T-F figures
41,720 / 7,472 present at the O1thr rev-3 brief (§9/L572). §2(ii)'s
"12 GREEN / 18 RED of 30" exact against the committed weld-probe output.

**No statement-level defect found at HEAD.**

---

## §5. CHARGE — the arc-accounting system

* **All 19 hashes resolve with matching subjects and grades** (the 18 of
  PE9's audit + PE9's own `b0b4c3a`, whose commit subject records "0
  CRITICAL, 0 GAPS, 0 minor — THE ARC'S FIRST CLEAN PASS", matching its
  §0). Every grade string in the note's S-STATUS/round-block/footer arc
  surfaces matches the corresponding report's verdict line.
* **Strike census recomputed by an independent method** (indented-display
  and inline-code stripping rather than PE9's backtick-token walk): 174
  `~~` tokens = **87 spans, 0 odd paragraphs** — the r8 census, toggle-clean.
* **Current surfaces:** all four CURRENT next-attempt surfaces (S-STATUS
  L165, r8 round block L1298, §7.3 CONSUMES L2678, footer L3101) say
  JB-PE9; every superseded S-STATUS/arc line is struck; the counter reads
  0/2 at 41 sites, all inside r8-dated records. **The note is one clean
  pass stale BY CONVENTION** — PE9 ran clean and clean passes do not edit
  the note (verifiers fix nothing; only repair rounds write); identical
  to the LIFTCORNER arc, where the note stayed at its r7 surfaces through
  two clean passes until the orchestrator's ★ ACCEPTANCE RECORD ★ was
  appended at the tail. Consistent, not a defect (see §7(a)).
* **Dating:** r8's "2026-08-08 campaign (wallclock 2026-08-06)" matches
  commit 49f9168 (2026-08-06 11:38); PE9 wallclock 2026-08-06 16:44.
* **No grade-promotion language anywhere**; JB-BOX-6's fences (no
  gr/carrier, no count/menu/density, P0 gate) intact.

**Arc accounting: CONSISTENT AND TRUE AT HEAD.**

---

## §6. PE9's three unscored observations, adjudicated independently

* **(a) Hard-wrap reflow convention** — AGREE, non-finding: my §4 quote
  checks applied the same wrap-agnostic reading the whole arc (including
  PE8's F-1 itself) has used; the r8 quotes are word- and
  character-content exact after unwrap.
* **(b) Round-record blocks retain historical "next attempt" lines** —
  AGREE, non-finding: the unstruck "JB-PE(n+1) next" closes of the r4–r7
  round blocks are dated records; all CURRENT surfaces are correctly
  struck-and-superseded; a contrary ruling would make every clean pass
  self-falsifying (the LIFTCORNER precedent, now doubly confirmed by that
  arc's accepted tail).
* **(c) JB-EPS's quantifier stricter than its proof needs** — AGREE,
  non-finding (harmless weaker claim); my §2 route adds the parallel fact
  for the u ≥ 0 theorem itself (holds on the whole cone, not only the
  lattice) — same genre, same harmlessness, see §7(b).

---

## §7. Observations (NOT scored — nothing here survives as a finding)

**(a) At acceptance, the S-STATUS "ZERO clean passes" line will need the
LIFTCORNER-style supersession.** The [r8] S-STATUS says "acceptance
counter 0/2 (ZERO clean passes)" — true when written, now one clean pass
stale (two if this pass stands). The convention resolves this at the
ledger action: the appended acceptance record (as in LIFTCORNER's tail)
becomes the current surface. Recorded so the orchestrator's fold does not
leave the S-STATUS as the last word.

**(b) An available strengthening at rows 4/12, not a defect.** Combining
§2's cone lemma (⊇) with PE7's j := s decomposition read at every m (⊆)
gives {V ∈ ℤ_{≥0} : u(V) ≥ 0} = {e_{m−1}A + h_{m−1}j : A, j ≥ 0} EXACTLY,
at every m. So the carried membership residue w_{q+1}(f) ∈ 𝒲_{q+1}
(sufficient, per the note) could be weakened to cone membership
w_{q+1}(f) ∈ 𝒞(e_q, h_q), which is EQUIVALENT to the needed proviso
instance — turning the "possibly strict at m ≥ 2" containment question
into the crisper "is 𝒲_m = 𝒞 ∩ (what the class attains)?" (𝒲_m ⊊ 𝒞
happens at concrete m = 2 read data, e.g. reads (2,3,1),(2,3,1) with
W₁ = 0, where 2 ∈ 𝒞 \ 𝒲₂). The note's current wording — sufficiency
carried, converse instance-dependent, strictness unproved in general —
remains honest and is CONFIRMED by this analysis; a future round could
display the cone identity if a consumer ever needs the exact form.

**(c) §7.2's JB-VTX grade cell closes with "[rows 7–13]", including
row 7 (JB-AFF), which has its own table row and its own §7.2 row.** A
pointer-range inclusiveness only (JB-AFF's content is exercised inside
(b)/(c), per its own row); no fence content rides on it; semantically nil.

---

*Pass artifacts: this report only. The instrument reruns reproduced the
committed artifacts byte-identically in place; my §2–§3 probe ran in-pass,
read-only, to /tmp. No other repository file was created or modified.*

— GRTJB-PE10, 2026-08-08 campaign (wallclock 2026-08-06), fresh context.
