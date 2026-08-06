# GRTJB passPE9 report — hostile verification pass (SEVENTH acceptance attempt)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` at HEAD after r8
(commit `49f9168`, THE ONE-QUOTATION ROUND). **Reader:** fresh-context hostile
verifier; fixes nothing; quote-and-classify. **Inputs read:** the full note at
HEAD (3,101 lines, top to bottom), the eight prior pass reports
(PE1 `85a8dc9` … PE8 `6c61b82`), the r8 diff (`git show 49f9168`, 5 hunks,
+89/−8), the r7 text (`4c4ee56`) for pre/post byte comparison, and the four
sealed instruments + committed artifacts in `verification/openmath/`.
**Note on the acceptance rule:** PE8 (0C+0G+1m) was NOT clean, so the counter
stood 0/2 entering this pass; a clean pass here STARTS the count.

---

## §0. VERDICT

**0 CRITICAL ERRORS, 0 JUSTIFICATION GAPS, 0 minor — CLEAN.**

This is the arc's FIRST clean pass (seventh acceptance attempt). Per the
acceptance rule the count starts at 1/2; the ledger/counter action is the
orchestrator's, not this report's. Three unscored observations in §6.

Machine legs 4/4: all four sealed instruments re-run at HEAD, exit 0, every
stdout **0-line diff** against its committed output (elapsed values
reproduced exactly), every rewritten JSON byte-identical to the committed
artifact (`git status`/`git diff -- verification/` empty after the reruns),
all four md5s at their sealed values. Figures vs the note: exact (§5).

---

## §1. CHARGE 1 — the r8 diff, line by line (5 hunks; the two per-site
quotes byte-checked against the struck originals myself)

The r8 diff touches exactly five sites, all disclosed in the commit message
and in the note's own [r8] surfaces; nothing else in the file moved
(diff-verified against `4c4ee56`; the commit touches only the note).

**(a) The ONE fix — the r7 F-1 bullet's fused quote (note L1218–1231).**
The bullet's quotation is struck in place and an [r8, PE8 F-1] bracket
supplies each site's actual struck wording. I byte-checked all three strings
myself against the live text at HEAD (whitespace-normalized for hard-wrap
reflow; see Observation §6(a)):

* Site A, §0M column (b) (L232–233), text under the [r6, m-1] strike:
  `per-instance a logically STRONGER hypothesis than the proviso, not an
  equivalent` — **matches the r8 bracket's site-A quote exactly** (word- and
  byte-content identical after unwrap).
* Site B, §5 SCOPE (L2095–2096), text under the [r6, m-1] strike:
  `per-instance a logically STRONGER hypothesis, not an equivalent or weaker
  one` — **matches the r8 bracket's site-B quote exactly**.
* The struck fused string (L1220–1221): `per-instance a logically STRONGER
  hypothesis than the proviso, not an equivalent (or weaker one)` —
  programmatically confirmed to be EXACTLY site A's wording with site B's
  extra words inserted parenthesized, i.e. the bracket's "FUSION" description
  is precise; confirmed the fused string appears at NEITHER site (site A
  lacks "or weaker one" ✓, site B lacks "than the proviso" ✓ — PE8 F-1's
  claim re-verified independently).
* The bracket's closing claim ("every disposition in this bullet — underived;
  FALSE at m = 1; STRUCK and replaced — applies to each site's verbatim
  wording") — TRUE: each site's wording contains the affirmative
  non-equivalence claim ("not an equivalent" / "not an equivalent or weaker
  one"), which is exactly what PE7 refuted at m = 1 and what r7 struck and
  replaced at both sites (both [r7, PE7 F-1] replacement brackets verified in
  place at L233–248 and L2096–2104).

**(b) [r7] S-STATUS struck, [r8] S-STATUS added (L112–169).** The wrap adds
one strike span; the new block's arc string reproduces all eight pass grades
and all repair-round commits correctly (every hash resolved and matched
against its commit subject and its report's §0 verdict line — see §2). Its
summary of PE8 is faithful: "0 CRITICAL + 0 gaps + 1 minor, NOT CLEAN; the
SIXTH acceptance attempt" ✓ (PE8 §0); "WIDER box than PE7's — 340 read data,
0 counterexamples" ✓ (PE8 L91–92: e₀ ≤ 9, h₀ ≤ 11 coprime, g₀ ≤ 5,
V ∈ [0, 400), 340 read data); "q+1 <= G.RANK conjunct re-read … redundancy
re-derived" ✓; "arc-accounting system verified consistent" ✓ (PE8 §3);
"the one finding is quotation-form … FUSED string … at NEITHER site" ✓
(PE8 F-1, quoted faithfully — no dropped qualifier). The r8 self-description
("note-only … ran NO probe … cites NO new machine figure") is TRUE of the
diff: every figure in the r8 hunks is a quoted prior figure with attribution.

**(c) New [REPAIR ROUND r8] block (L1280–1300).** Content matches (a) and
(b). Its strike-census claim "83 → 87 spans (the four r8 spans: the fused
quote, the [r7] S-STATUS wrap, the §7.3 [r7] counter clause, the footer r7
Arc line)" — INDEPENDENTLY RECOMPUTED: at `4c4ee56` the note has 166 `~~`
tokens outside backticks = 83 spans, 0 odd paragraphs; at HEAD 174 tokens =
87 spans, 0 odd paragraphs (toggle-clean both). The four new spans in the
diff are exactly the four named: (1) the fused quote, (2) the [r7] S-STATUS
wrap, (3) the §7.3 CONSUMES parenthesis's "[r7] seven hostile passes …
JB-PE8 is the next acceptance attempt" clause, (4) the footer [r7] block's
"Arc: PE1 … 0/2." line. Census claim EXACT. "6 [r8 brackets" ✓ (grep: 6).
"+89/−8" ✓ (diff stat).

**(d) §7.3 CONSUMES acceptance-counter parenthesis (L2671–2678).** [r7]
clause struck, [r8] appended: "eight hostile passes run, eight repair rounds
applied; JB-PE9 is the next acceptance attempt" — TRUE at HEAD.

**(e) Footer [r7] block's Arc line struck; [r8] footer block appended
(L3078–3101).** The [r8] block's PE8 summary matches (b); its arc line adds
"PE8 (0C+0G+1m) → r8 → JB-PE9 = the next acceptance attempt; counter still
0/2" — grades verified against PE8's §0. Instruments-byte-frozen claim
verified (§5).

**Verdict on the r8 diff: EXACT.** The one fix does what it says; every arc
surface it syncs is true at HEAD; no identity, fence, frontier, census, or
grade moved (hunk-by-hunk check: every hunk is strike, bracket-annotation,
or arc record).

---

## §2. CHARGE 2 — the arc-accounting system at HEAD

* **S-STATUS chain (L8–169):** seven struck blocks (r1…r7) + [r8] CURRENT,
  which correctly says "supersedes the seven struck lines" (count verified:
  exactly seven struck S-STATUS blocks precede it). Eight passes, eight
  rounds, counter 0/2, JB-PE9 next.
* **All 18 commit hashes resolve with matching content:** PE1 `85a8dc9`
  (1C+9G) · r1 `4c97649`,`46f9452` · r2 `67bf0c4`,`888e293` · PE3 `2fd271e`
  (0C+8G) · r3 `8acb2d1`,`87c553d` · PE4 `38c4754` (0C+8G) · r4 `ae0acdf` ·
  PE5 `39e16ee` (0C+5G) · r5 `f9f104e` · PE6 `ca39044` (0C+2G+1m) · r6
  `4607824` · PE7 `aa9b603` (0C+1G+2m) · r7 `4c4ee56` · PE8 `6c61b82`
  (0C+0G+1m) · r8 `49f9168`. Every grade string in the note's arc surfaces
  matches the corresponding report's own §0 verdict line, re-read at source
  (PE2 "0 CRITICAL, 7 JUSTIFICATION GAPS" … PE8 "0 CRITICAL, 0 JUSTIFICATION
  GAPS, 1 MINOR").
* **All four "next attempt" CURRENT surfaces agree:** S-STATUS (L165), the
  r8 round block (L1298), §7.3 CONSUMES (L2678), footer arc (L3101) — all
  say JB-PE9. The only "JB-PE8 next" strings left live sit inside dated
  round-record blocks (see Observation §6(b)); every superseded CURRENT
  surface is struck.
* **Strike system:** 87 spans, toggle-clean (0 odd paragraphs), matching the
  r8 block's census; 83 at the r7 pin — delta exactly r8's four.
* **Dating:** "2026-08-08 campaign (wallclock 2026-08-06)" — commit
  `49f9168` is dated 2026-08-06 11:38 UTC ✓; footer sign-off line and
  §7.3/footer datings consistent.
* **Fences:** counter 0/2 everywhere; "no gate fires; no acceptance arc is
  open" consistent with the grade cap and JB-BOX-6 (row 28: counter 0/2, P0
  gate stands); GRTW2/J-A consumed at attempt grade as before — no
  grade-promotion language anywhere in the r8 diff.

**Arc accounting: CONSISTENT AND TRUE AT HEAD.**

---

## §3. CHARGE 3 — decorrelated re-derivation: LEMMA JB-EPS's integer
identity by the FLOOR-COCYCLE route (a route no prior report used)

**Component chosen:** LEMMA JB-EPS (§5, L2171–2184) — the ε-cocycle
collapse, the lemma powering THEOREM JB-CREAD's carry cancellation (the
note's headline z_m^{−ε′}·z_m^{ε′} = 1 step).

**How every prior route went:** the note's own proof telescopes the
numerator ℓ(V+V′) − s(V+V′) − ℓV + s(V) − ℓV′ + s(V′) = s(V)+s(V′)−s(V+V′)
and then CITES the carry clause JA-GRID(c) = (C-EPS) for
s(V)+s(V′)−s(V+V′) = e_{m−1}·ε′. PE1 (§2.2) verified exactly this route:
it re-checked the telescope, pulled JA-GRID(c)'s statement and J-A's
congruence-and-range proof of it, and concluded "its only non-elementary
input is JA-GRID(c)". PE2/PE3 re-confirmed the same chain; the runner's leg
(family JB-EPS, 955 samples) checks the same identity numerically via
`s_geo`. No pass derived the identity any other way.

**My route (used by no report and not by the note): identify the twist
exponent as a floor and take the cocycle defect of the floor function.**
All symbols the note's (§5 notation block, r1/G-7): e := e_{m−1} ≥ 1,
h := h_{m−1} with gcd(e,h) = 1, ℓ := ℓ_{m−1} any integer with ℓh ≡ 1
(mod e); s(β) := (ℓβ) mod e (canonical representative in [0, e));
t_m(β) := (ℓβ − s(β))/e.

1. **t_m is a floor.** By the definition of the canonical mod,
   ℓβ = e·⌊ℓβ/e⌋ + (ℓβ mod e) for EVERY integer ℓβ (either sign), so
   t_m(β) = ⌊ℓβ/e⌋. (Integrality — the note's "divide by e_{m−1} is
   legitimate" step — is automatic in this presentation.)
2. **The floor-carry identity.** For all integers a, b and e ≥ 1:
   ⌊(a+b)/e⌋ − ⌊a/e⌋ − ⌊b/e⌋ = ⌊((a mod e) + (b mod e))/e⌋.
   *Proof:* write a = e⌊a/e⌋ + (a mod e), b likewise; add; divide the sum's
   floor decomposition. ∎ (Two lines, pure integer arithmetic.)
3. **Apply at a = ℓV, b = ℓV′:** a mod e = s(V), b mod e = s(V′), so
   t_m(V+V′) − t_m(V) − t_m(V′) = ⌊(s(V)+s(V′))/e⌋ = ε′ — LEMMA JB-EPS's
   integer form. The field form follows as in the note (JA-EPS's convention
   ε_m(β) = z_m^{−t_m(β)}, an exponent bookkeeping step, unchanged).
4. **Representative-independence (a check the other routes never needed to
   make explicit):** replacing ℓ by ℓ + ke changes t_m(β) by kβ, and the
   cocycle defect by k(V+V′) − kV − kV′ = 0 — the identity is independent
   of the choice of inverse representative, as it must be.

**How this differs from every used route:** (i) it never routes through the
telescoping decomposition; (ii) it consumes JA-GRID(c) NOWHERE — instead the
carry clause s(V)+s(V′)−s(V+V′) = e·ε′ falls out as a corollary of steps
1–3 (multiply the defect by e), so the "only non-elementary input" of the
note's proof is here derived rather than cited; (iii) it proves the integer
identity for ALL V, V′ ∈ ℤ_{≥0} (indeed all of ℤ), a strict superset of the
note's lattice-restricted quantifier "V, V′ ≥ 0 in the level-m weight
lattice" — so the lemma as stated is a (harmless) weakening of what its own
definitions force; the stated quantifier is sufficient for its one consumer
(the (λ, γ_{m+1}) instance, licensed by (Ĉ-wt)). Conclusion: the note's
LEMMA JB-EPS and its §5 application are CONFIRMED by an independent
derivation; the note's own proof, and its unconditional grade (§0M row 19),
are also correct as written.

**Fresh machine leg (my own implementation — no runner code, no `s_geo`,
no JSON reuse):** exhaustive check over e ∈ [1,12], all h coprime to e in
[1,12], ℓ ∈ {ℓ₀ − 2e, ℓ₀, ℓ₀ + 5e} (representative-invariance leg), V, V′
sampled over [0,60]: **31,941 checks — 0 violations** on all four asserted
identities (t = ⌊ℓV/e⌋; cocycle defect = ε′; carry clause = e·ε′;
rep-invariance of the defect), with the observed ε′ value set exactly
{0, 1}. Spot-confirmed the superset point at the note's own corollary
instance: V = V′ = 1 at (e,h) = (2,3) — OUTSIDE 𝒲₁ per §5's corollary —
still satisfies the identity (defect 1 = ε′ 1). Read-only, run in-pass;
no repository file touched.

---

## §4. CHARGE 4 — statement-level truth sweep of the four theorem boxes
(fences read as part of each statement)

**THEOREM JB-DEV (§2).** (i) uniqueness-of-division content at the
admissible representative — sound; W2-C1 ride disclosed at the statement.
(ii) byte clause: hypothesis IS `P≤q` (§0M row 2) — stated as its own
hypothesis, honest. (iii) per-layer fences as displayed: (VAL)/(GRID) on
`P<q` (0 ≤ q ≤ qcap), (RES) on `P≤q` one level deeper (r3/F-4), (GRID)
additionally on JA-GRID(a)'s u ≥ 0 proviso — narrowed r5/F-3 to the
membership residue at the unbounded-degree quantifier, with the r7-corrected
instance-honest relation now at both carrying sites (verified: no
overstating "exactly"/"not an equivalent" survives anywhere live — grep
swept). (RES)'s no-machine-leg disclosure present (row 5). (iv) displayed
fence, cited not claimed. The r1/F1 reading fence ((VD-m) ≠ JA-RES) intact
with the r2/G2-4 data-not-mechanism wording. **TRUE AS FENCED.**
**THEOREM JB-VTX (§3).** Head restated at 0 ≤ q ≤ qcap. (a) I re-derived
the displayed shear arithmetic: u_i = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})
(print monomial ordinates), so e_q·u_i + h_q·i = e_q·w_q(A_i) + i·γ_{q+1}
via JA-VAL + γ_{q+1} = e_q·w_qΦ_q + h_q ✓. (b) via JB-AFF (a > 0 affine
abscissa-preserving map, chord order preserved) ✓. (c) slope σ ↦ e_qσ + h_q
(substitute u = σi + c into the sheared ordinate) — realized side −h_q/e_q
↦ 0, lattice data preserved ✓. (d) the three-way tie split honest: (d1)/(d2)
on `P<q` with the runner's shared_upto gate on (d1) disclosed as an
instrument cut; (d3) = JA-VAL at level q+1 on `P≤q` (r6/F-1), the gate
coinciding with the fence; (d4) grid/read content carries the u ≥ 0
membership residue AND the no-leg disclosure (row 12). (e) subject corrected
to the key (r1/G-4). **TRUE AS FENCED.**
**THEOREM JB-TREE (§4).** (i)/(ii) perimeter-free (uniqueness of division at
the print's own keys); the (ID-(i+1)) digit-list argument re-checked: for
k < g_i, e_i·k ≤ e_i(g_i −1) < P_i and deg C_k^{(i)}Φ_i^{e_ik} < P_i·deg Φ_i
= deg Φ_{i+1} (C_k reduced), so the development reads off uniquely ✓; the
r5/F-2 exit-bound-node scoping of the L-CELL gloss stands. (iii) the r4/F-4
re-scope intact: per-edge laws of the LINE functional, line = w_m = v_{m+1}
at R-leaves only, internal-edge transfer recorded NOT derivable in-list with
the candidate route NOT TAKEN. (iv) transported instance riding §5's fences
in full; (C-W_Q) no-leg disclosed. (iii)/(iv) at m ≤ qcap. **TRUE AS
FENCED.**
**THEOREM JB-CREAD (§5).** The five-line chain re-verified line by line
(eighth reading, still exact): (VD-m) at f gives ρ_m(f) = ε_m(λ)v; v ≠ 0 and
τ_m a unit force the on-line cell (L-CELL(ii)) whence w_m(R) = λ + γ_{m+1}
with (C-W_R); (VD-m) at R + (C-READ) + τ_m = ε_m(γ_{m+1})^{−1}c_m + JB-EPS
at (λ, γ_{m+1}) — whose ε′ is verbatim [RMG] S0.2's — collapse the carry.
My §3 re-derivation independently underwrites the JB-EPS step. The (VD-m)
hypothesis honestly required at BOTH f and R; unconditional at m ≤ 1 ONLY;
v = 0 branch scoped to read-at-target and machine-unexercised (disclosed);
the setting's three Ĉ_m clauses present (r3/F-5); the license derivations
(λ, γ_{m+1} ∈ 𝒲_m) one line each from the r4/F-8 definition ✓; the §5
four-line u ≥ 0 theorem re-checked against the lattice description (steps
(1)–(4) all verified again). **TRUE AS FENCED.**

Cross-checks: each box's per-clause grade display matches its §0M rows
(rows 1–13 vs §2/§3; 14–18 vs §4; 19–23 vs §5 — spot-verified cell by cell
at rows 3/4/5/11/12/19/20/21/22); the footer's "JB-DEV(i)/(ii)/(iv) hold at
every q ≥ 0" is consistent with §2's actual clause structure (a clause (iv)
exists, L1539). **No statement-level defect found.**

---

## §5. MACHINE LEG — all four instruments at HEAD

All four scripts re-run from the committed tree (md5s checked before and
after; `git status`/`git diff -- verification/` empty after the runs — the
rewritten JSONs reproduced byte-identically, elapsed fields included):

| instrument | md5 (sealed value) | exit | stdout vs committed output |
|---|---|---|---|
| `grt_jb_checks.py` | `55f4911eaddd8524fd91368b30ed71bd` ✓ | 0 | 0-line diff |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` ✓ | 0 | 0-line diff |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` ✓ | 0 | 0-line diff |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` ✓ | 0 | 0-line diff |

Figures vs the note, re-read from the fresh stdouts: 6,700 samples, 0
violations, all 18 families GREEN, teeth CAUGHT (verdict block verbatim);
JB-CREAD scored 104 / boundary 21 with the census cross-check 13 + 8 = 21 ✓;
JB-EPS 955, JB-VTX 893, TW-JB 2,480 ✓ (§0M/(f) cells); MJB-CREAD teeth
material 22 ✓ (row 23's "22 designated samples"); print walker 458 samples,
84 walks, PW-XFRAME 72 = 45 + 27 decomposition ✓, ALL GREEN; printwalk2
45/45 agreed with non-degeneracy certificates + 27 degenerate certified +
28 recon, GREEN ✓; level census: roster boundary 13 (m=1: 0, m=2: 10,
m=3: 3), scored 56, scope-outs 0, sealed-census cross-check 21 ✓ — exactly
the note's §7.1/§7.4 and F1-readout figures.

---

## §6. Observations (NOT scored — no finding survives verification)

**(a) "byte-exactly" and hard-wrap reflow.** The [r8, PE8 F-1] bracket's two
per-site quotes are word- and character-exact after unwrapping, but the
markdown hard-wrap breaks fall at different columns than the originals
(unavoidable at different indentation). Every quote verification in this arc
— including PE8's F-1 itself, which was about missing/extra WORDS — has
applied the wrap-agnostic reading, so this is convention-consistent, not a
defect. Recorded so a future pass does not re-litigate it.

**(b) Round-record blocks retain their historical "next attempt" lines.**
The r4–r7 round blocks (L1034/1107/1196/1277) still close with "JB-PE(n+1)
… is the next acceptance attempt" unstruck. These are dated round RECORDS —
the same convention every prior pass accepted (and the LIFTCORNER PE9
acceptance pass explicitly adjudicated for the sibling arc: a contrary
ruling would make every clean pass self-falsifying). All CURRENT surfaces
(S-STATUS, §7.3 CONSUMES, footer arc) are struck-and-superseded correctly.

**(c) JB-EPS's quantifier is stricter than its proof needs.** My §3 route
shows the integer identity holds for ALL V, V′ ∈ ℤ_{≥0}, not only lattice
members; the note's lattice-restricted statement is therefore a weaker
claim than available — harmless (the restriction costs no consumer
anything, and the r4/F-5 record already documents that the machine leg
samples plain integers). PE8's standing observation on "possibly strict at
m ≥ 2" (a future round could display the settled instance-dependent record)
remains open at its PE8 grade; the current wording stays honest.

---

*Pass artifacts: this report only. No repository file other than this
report was created or modified by this pass; the instrument reruns
reproduced the committed artifacts byte-identically in place. My §3 probe
ran in-pass and read-only.*

— GRTJB-PE9, 2026-08-08 campaign (wallclock 2026-08-06), fresh context.
