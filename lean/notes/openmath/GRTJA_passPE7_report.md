# GRTJA pass PE7 — seventh hostile pass (acceptance attempt at 0/2, post-r5) on GRTJA_PROOF_2026-08-08.md

**Verifier:** JA-PE7 (fresh hostile Fable context; fixes nothing). The
acceptance attempt after the r5 repair: a clean pass here starts the
2-consecutive count (counter action = orchestrator's).

**Target pin:** note at HEAD (repo HEAD 436b9c6), md5 `cba309ce` ==
`git show f131c53:` (the JA-r5 repair commit — the note's last commit; no
uncommitted drift; `git log f131c53..HEAD` over the note + all three J-A
artifacts + the rescued Lean leg = EMPTY across 9 post-r5 commits).
Artifact seals verified by md5 at worktree AND pins: runner
`grt_ja_checks.py` `5972d412` == @696eae8 (SEAL); output `0d6d0522` and
JSON `13ab52ab` == @1cbf8ca (VERDICT); `ja_pe6_lean_leg.lean`
`52a81e63` == @9dfd8fc (the r5-recorded rescue — REAL, at the named
commit, md5 exact). The r5 round was note-only as claimed ("Runner +
artifacts BYTE-FROZEN" TRUE; commit stat: 1 file, +80/−8). Supplier
state at HEAD: `GRTW2_PROOF_2026-08-08.md` last commit = **94534df**
(2026-08-07 14:20, = W2 r4) — exactly the [JA-r5] as-of pin, and the W2
note has NOT moved since (W2 PE5's CLEAN report ba2c47c, 15:03, is
note-motion-free); `ITERLAWN_PROOF` and the JB note both moved at the
FOLD commit **5054d69** (15:10, 23 minutes AFTER r5) — blast radius
verified nil below (observation q1); blueprint (00ce2b6), completion
tree (46e583e), `grt_weld_probe.py`, `iterlawn_pe_reimpl.py` motion-free.

**Charge executed:** (1) the r5 diff line-by-line, with the two as-of
quotes BYTE-CHECKED against `git show 94534df:` and every timeline fact
checked against git (§2); (2) the arc-accounting system at HEAD after
six rounds, every live surface swept (§3); (3) ONE fresh re-derivation
by a route unused across all six prior reports: the UNIMODULAR-MATRIX
(GL₂(ℤ) change-of-basis) route with a group-algebra generating-function
leg for the carry clause (§4); (4) statement-level truth of the four
theorem displays at HEAD (§5). Machine leg re-run in a /tmp sandbox
(committed artifacts untouched).

---

## 1. Machine leg — RE-RUN, BIT-IDENTICAL MOD TIMING

Re-ran `grt_ja_checks.py` (full battery, /tmp copy with all 13
engine_ext pinned artifacts; PARI leg live): **exit 0, all 17 families
GREEN, TOTAL samples 10,311, 0 violations, CK-RES boundary 16, CK-BPREF
26, elapsed 5.4 s**; stdout 54/54 lines identical to the committed
output after stripping wall-clock fields (mechanical strip-compare:
True); regenerated JSON deep-compared key-for-key against the committed
`grt_ja_checks_results.json`: **identical except `elapsed_s`** (5.4 vs
7.4); `violations` empty in both. Censuses recounted from the COMMITTED
JSON by my own arithmetic: main-roster scored sums to **396**
(13+12·6+19+34+19+20+17+40+60+76+26), + QO 14 (0/7/0/7/0) + d₀ 33
(8/8/9/8) = **443** = the CK-RES/CK-VDM samples cell; boundary **16 =
main 9 (T3B 4 + I4B 5) + transported 7 (T3B 3 + I4B 4)** read from the
per-tag `tw` records, every other instance 0; bpref **26 = 22 roster
hits on exactly 10 rows** (T2A/T2C/T2D/T2G 1 each, T3A/T3C/T3D 2 each,
T3E 4, T3F 1, I4C 7) **+ 4 d₀ hits** (one each); family samples column
== §7.1 cell-for-cell (1/111/1,132/872/1,744/3,248/340/443/443/26/444/
1,452/5/4/3/2/2); QO 5/5 `complete` with `pari_full` ((4,1),)×3,
((2,2),), ((3,1),); TW-INST ledgers exactly 20; teeth 8/9/8, 11/11,
12/18 on the designated rows. Every §7.1 figure confirmed.

## 2. Charge 1: the r5 diff, line-by-line — FAITHFUL AT ALL EDIT SITES; BOTH QUOTES BYTE-EXACT AT 94534df

The r5 diff (`git show f131c53`) touches exactly: the header genre line
(round 6 = JA-PE6 added with the verdict figures; next pass = JA-PE7),
the §7.3 fence (rounds 1–6 inventory + "next = PE7, the acceptance
attempt, [r5]"), the §8 heading ("(rounds 1–2)" → "(rounds 1–6)"), the
[JA-r5] bracket at the r4 record's m1 clause, and the appended r5 round
block — PE6's two findings + the round block, note-only, exactly as
billed. Verified:

* **The two as-of quotes vs `git show 94534df:GRTW2_PROOF` —
  BYTE-EXACT** (whitespace-normalized mechanical compare, both MATCH):
  (i) the W2-C3 claims-table row's [r3] bracket "W2-ID1/(OPEN-2a) carry
  the FORWARD direction only (recorded ξ = 1 ⟹ byte-equal, so nothing
  byte-RED below the first recorded twist — all the proved scope needs);
  the converse is unproved at every m, PE3's counter-instance recorded
  at §5.2" sits verbatim at the pin's line 980, ON the exact
  (OPEN-2a)/W2-ID1 clause JA's clause 8 carries (as billed); (ii)
  §6.3(d)'s re-scope, correctly attributed "[r4, PE4-P1]", is verbatim
  at the pin ("the FORWARD direction of the recorded-ξ/byte-divergence
  identification at m ≥ 2 … the CONVERSE (recorded ξ ≠ 1 ⟹ byte-RED) is
  UNPROVED at every m …").
* **Timeline facts vs git, all EXACT:** W2 r3 = 79d1d9c 09:31:14; JA r4
  = debf99d 09:46:49 (15 minutes ✓); the dispatching commit a48c22d
  09:44:33 dispatches "W2 PE4", presupposing the W2-r3 landing ✓;
  94534df = W2 r4, 14:20:00, the W2 note's last commit at r5 (14:47:46)
  — "the supplier's HEAD at this repair, post-W2-r4" ✓; and the W2 note
  is STILL at 94534df at my HEAD, so the pin sits at the supplier's
  current HEAD too.
* **The bracket's blast-radius claims independently re-verified, all
  three ways:** (i) the blanket as-of pin [W2 @ ffa1e57] covers clause
  8's consumption (the [JA-r3] bracket, unchanged); (ii) W-2 §6.3 is
  byte-IDENTICAL between ffa1e57 and 79d1d9c (my own section diff:
  True), and the ONLY §6.3 motion at 94534df is the (d)-item forward-only
  re-scope itself — the weakening direction, diff-verified; (iii) no JA
  derivation rides the converse (own read: §3's proofs consume
  W2-L0/L2/L3 only — lemma-level, consumed proved; the transported
  chamber is billed instance evidence + TW-INST, not derivation).
* **The r5 round block vs the PE6 report (8b2fbed):** verdict figures
  (0C, 2 JG both minor both arc-accounting, 0 minor; counter stays 0/2)
  ✓; machine-leg figures ✓; the 19-declaration Lean-leg inventory
  matches PE6 §4 item-for-item ✓; FINDING 1/FINDING 2 restatements
  exact (incl. timestamps and "PE5 FINDING 1's own species") ✓;
  observations (p1)–(p3) restated with p4 marked EXECUTED by the rescue
  ✓ (PE6 listed p1–p4; p4 was the seal-the-Lean-leg offer — the rescue
  at 9dfd8fc with md5 preserved IS its execution, verified above).
  "Grade changes: NONE" TRUE (no §7.2 row, grade cap, or ∎-grade
  touched by the diff). "Note-only" TRUE (commit stat).
* **Header inventory:** "round 6 = JA-PE6 (0 critical + 2 justification
  gaps (both minor, both arc-accounting), repaired at r5 below)" — exact
  vs the PE6 report; counter 0/2; next pass = JA-PE7 ✓.
* The 'Clause 8's carried "(OPEN-2a) … proved only at m = 1 (W2-ID1)"
  is henceforth read with that one-direction scoping' sentence is the
  PE6-cure's "carry the one-direction-only scoping" executed as a
  reading rider on the pinned consumption — see observation q3 on its
  location.

## 3. Charge 2: the arc-accounting system at HEAD — CONSISTENT AND TRUE

Live surfaces at HEAD: header genre line TRUE (rounds 1–6, counter 0/2,
next pass = JA-PE7); grade cap TRUE (untouched); §7.3 fence TRUE
(rounds 1–6 inventory exact against git, [r5]); **§8 heading "(rounds
1–6)" TRUE** (PE6 FINDING 1 cured; the section records rounds 1–6: r1,
r2, r3 = rounds 3–4, r4, r5); ledger live line TRUE
(`BRIDGE_ADJUDICATIONS_2026-07-30.md` line 11672: "JA 0/2 (PE7 =
attempt)"). Round facts vs git ALL EXACT: PE1 5e70442 → r1 ce0469a →
PE2 9040961 → r2 5d95805 → PE3 c77ae6f (CLEAN, 1/2 at a83c108) → PE4
535e79f (0C+1G, reset) → r3 8ee86da → PE5 6a216b9 (0C+1Gm) → r4 debf99d
→ PE6 8b2fbed (0C+2Gm) → r5 f131c53. Grep sweep of every arc token
("next pass"/"next ="/"rounds 1–"/"0/1"/"1/2"/"0/2"/"no acceptance
arc"): every hit is inside a dated bracket, the struck r1 tail, a
round-stamped record tail (the six-pass convention), or a true live
surface — the PE5/PE6 stale-surface species is EXTINCT at HEAD.
**Fired-trigger sweep** (the PE6 FINDING 2 species): every deferral in
live text checked against git for a fired trigger — NONE found riding
one at r5 write time. The two post-r5 supplier motions (the fold
5054d69 at 15:10; W2 PE5 CLEAN at 15:03 advancing the W2 counter to
1/2) both POSTDATE r5 (14:47) and no JA repair round has occurred
since, so the PE4-n3 staleness convention (which lapses only when a
repair edits the note — the standard PE5/PE6 enforced) excuses the
affected surfaces; both motions are in the favorable direction
(observations q1/q2). ILN blast radius checked directly: the fold annex
is append-only and **S0.1/S0.2 — everything JA consumes — are
byte-identical since the ced7dbb pin** (own section diff); the JB fold
errata E-1 explicitly adopts JA's root-inclusive (R-coll) form and E-2
defers W2-C3 grades to supplier HEAD ≥ 94534df — both consistent with
JA's pins and carried scopings.

## 4. Charge 3: fresh re-derivation — THE UNIMODULAR-MATRIX ROUTE (unused by PE1–PE6)

Prior routes: PE1 direct subtraction (field identity) + hand instances;
PE2 witness construction + sealed-engine probe; PE3 recursion-tree walk
+ QO/d₀ vein; PE4 ν-shift/covariance + exact grid interpolation +
conjugation probe; PE5 coset master lemma + engine-free Euclid probe;
PE6 the Lean kernel. NEW ROUTE — the entire §3/§4 exponent system read
off ONE object, the unimodular matrix of the read: with normalized
Bézout ℓh + ℓ′e = 1, set **M := [[h, e], [ℓ′, −ℓ]]**; det M = −1, so
M ∈ GL₂(ℤ) with M⁻¹ = [[ℓ, e], [ℓ′, −h]], and (V, T) := M(X, Y) is a
ℤ²-bijection. Hand corollaries, each re-derived in full this pass:

* **Master lemma** = the T-parametrization of the fiber {hX + eY = V}:
  integer points are exactly (ℓV + eT, ℓ′V − hT), T ∈ ℤ — both
  directions from unimodularity alone, no coset argument.
* **JA-GRID(a)**: s = ℓV mod e at T = −t, t = ⌊ℓV/e⌋; u = ℓ′V + ht ∈ ℤ
  (W2-L0 integrality built into the parametrization); least-abscissa by
  the period-e spacing; u ≥ 0 ⟺ sh ≤ V (the proviso's exact content),
  counter-instance (2,3,1) ⟹ (ℓ,ℓ′) = (1,−1), u = −1 reproduced.
* **JA-EPS in ONE LINE**: ℓ′s − ℓu = (row 2 of M)·(s, u) = T = −t — the
  ε-exponent IS the lattice T-coordinate of the eq12 point; the two
  claimed-equal exponents are two expressions of one matrix coordinate
  (no fraction subtraction, no Bézout split).
* **W2-L2 covariance**: the weight shift kW pulls back to the lattice
  vector M(0, W/e) = (W, −A), A = ℓW/e — s invariant, t ↦ t + kA, both
  read off one vector; negative k included.
* **JA-RES per-slot exponent**: t(i) − τ = −iA from the covariance at
  the digit's own line (Def-t(i) sign; the shared s cancels exactly as
  the note's §3.4 display cancels it).
* **THE ORBIT ACTION IS A ROW OPERATION**: ℓ ↦ ℓ + κe forces
  ℓ′ ↦ ℓ′ − κh, and M_κ = R_κ·M with R_κ = [[1, 0], [−κ, 1]], hence
  T_κ = T − κV — §4(iii)'s t ↦ t + κβ AND ORB-RES's t(i) ↦ t(i) − κu_i
  are the SAME identity read at the two sign conventions/lines; s
  invariant since ℓ_κ ≡ ℓ (mod e); the grid form's −κu₀ + jκh from
  u_{i_j} = u₀ − jh. No prior pass derived the transport this way.
* **JA-GRID(c) via a GENERATING-FUNCTION leg**: in ℤ[x]/(x^e − 1),
  x^{s(V)}·x^{s(V′)} = x^{s(V+V′)} with the carry δ = the exponent-fold
  count — δ ∈ {0,1} and δ = 1 ⟺ s + s′ ≥ e drop out of monomial
  bookkeeping (the lattice-crossing reading, literally).
* **A_m = 0 ⟺ e_{m−1} = 1** (ℓ = 0 ⟺ e = 1 under normalization, with
  A = ℓgγ, g, γ ≥ 1) and the conjugation split iA = s₀A + j(eA).

**Machine leg** (`ja_pe7_matrix_probe.py`, /tmp, md5 `8fd286d0`,
disclosed uncommitted, same discipline as the PE2–PE5 probes): NO repo
import, NO pools, own brute-residue-scan Bézout (a THIRD Bézout
technology after PE4's `pow(h,−1,e)` and PE5's iterative Euclid);
exhaustive box e, h ≤ 12 coprime × V ∈ −30..60 PLUS 400 random reads
(e, h ≤ 60, |V| ≤ 10⁹, k, κ negative through positive). Families: M0
unimodularity/M·M⁻¹ 491; M1 master lemma both directions 257,760; M2
two eq12 technologies agree + line membership 2,783; M3 ε-exponent =
row-2 coordinate 2,783; M4 least-abscissa 2,783; M5 covariance + the
lattice vector (W, −A) 16,281; M6 group-algebra carry 6,981; M7
per-slot exponent 11,132; M8 orbit row-operation (matrix identity
R_κM = M_κ checked as matrices) 13,081; M9 A = 0 ⟺ e = 1 491; M10
conjugation split 8,349; M11 the (2,3,1) counter-instance — **TOTAL
322,916 checks, 0 violations, exit 0.** Every §3.2/§3.3(a)(c)/§3.4
(integer layer)/§4(ii)(iii)(iv)/§1 display confirmed by a mechanism no
prior pass used. (Content necessarily overlaps PE5's coset lemma — same
theorems — but the derivation mechanism is new: change-of-basis, not
coset characterization; the orbit as R_κ; the carry as group-algebra
overflow.)

## 5. Charge 4: the four theorem displays at HEAD — STATEMENT-LEVEL TRUE

* **JA-VAL (§3.1).** Re-walked: base w₀ = v₁ (both min coefficient
  valuation); step: shared keys ⟹ same canonical division ⟹ same
  digits; IH identifies the arguments of the two identical integer min
  recursions, v_{m+2}(φ_{m+1}) = γ_{m+1} by clause 7; the `propertiesv`
  φ-adic-development hypothesis carried in the display. Outside the
  matrix route's reach (min recursion, as it was outside PE6's Lean
  leg); machine CK-VAL 1,132/0 re-ran GREEN. TRUE as fenced (shared-key
  perimeter, grade line).
* **JA-EPS (§3.2).** = the T-coordinate identity at full generality
  (§4, M3); the SIGN CONVENTION display re-verified at source THIS pass:
  tex 1200–1201 carries the construct-child (ℓu − 𝔰)/e exponent and tex
  1432–1438 defines t(i) with the opposite sign (s − ℓu)/e, exactly as
  displayed; k-grid clause = M5 with the displayed hypothesis list. TRUE.
* **JA-GRID (§3.3).** Proviso u ≥ 0 displayed with the (2,3,1)
  counter-instance (M11; 1,194-instance non-vacuity was PE5's, my box
  reproduces the species); (a) = master lemma + least-abscissa +
  integrality (M1/M2/M4); the r1/r2 scoping brackets fence the discharge
  sentence to print-side sites with JB's col-(b) truth at its 4c4ee56
  pin (byte-verified by three prior passes; pin-protected against the
  post-r5 JB motion, whose E-1/E-2 errata point AWAY from any JA
  conflict); (c) = M6 exactly, incl. δ ∈ {0,1} and the ⟺; single-level
  fence displayed. TRUE as fenced.
* **JA-RES (§3.4).** Integer core = M7 (+ M8/M10 for §4); field step:
  proviso ⟹ R_{m−1}(a_i)(z) = z^{−τ}·C_i ⟹ c_i = z^{t(i)−τ}·C_i =
  z^{−iA}·C_i — one substitution, any field; m = 2 unconditional via
  (VD-1) = W2-L3 (consumed proved); JA-VDIND forward + root-inclusive
  (R-coll) [r2] stood four independent census reproductions and CK-VDM
  443/0 re-ran GREEN; the honest converse-unsealed and single-slot
  fences intact; JA-MIN rides with its in(f)-leg-OPEN rescope. TRUE as
  fenced. (Grades line and §7.2 rows unchanged by r5 — consistent.)

Cross-checks NOT graded: §2 clause 8's carry-list byte-faithful to W-2
§6.3 at the ffa1e57 pin (re-verified; the pin-to-HEAD §6.3 delta is
exactly the r4 forward-only re-scope the [JA-r5] bracket quotes); the
grade cap's "attempt grade" for W-2 still correct at HEAD (W2 at 1/2,
not accepted); W-2 §3.1's inherited 1213–1218 range still stands at
94534df (the [JA-r1] "cure owed to that note's own arc" remains
accurate).

---

## FINDINGS: NONE (0 critical, 0 justification gaps, 0 minor)

**Ungraded observations (recorded, not graded):**

* (q1) **Post-r5 supplier motion at the fold commit 5054d69** (15:10,
  23 minutes after r5): ITERLAWN gained the NR-1 rider-rewrite annex
  (append-only; S0.1/S0.2 — JA's whole consumption — byte-identical
  since the ced7dbb pin, own diff) and JB gained two dated errata (E-1
  adopts JA's root-inclusive (R-coll); E-2 defers W2-C3 grades to
  supplier HEAD). The §1 [JA-r3] bracket's "ITERLAWN_PROOF motion-free
  since" and the r2-era "owed at the fold" deferrals are now
  round-stamped history whose trigger has FIRED — no repair round since,
  so the PE4-n3 convention excuses them AT THIS PASS, but any future
  repair round owes the dated fold-executed brackets (the PE6-FINDING-2
  species otherwise re-arms).
* (q2) §5's W-2 bullet "(0/2 hostile passes)" became stale at 15:03
  (W2 PE5 CLEAN → supplier counter 1/2) — post-r5, favorable direction,
  same convention and same future-repair obligation as q1.
* (q3) Clause 8's (d) live text still displays the pin-faithful
  two-sided "identification … proved only at m = 1 (W2-ID1)" while the
  one-direction reading rider sits only in §8's r4-record [JA-r5]
  bracket ("henceforth read with that one-direction scoping") — the
  executed cure matches PE6's one-bracket spec, but a §2-local pointer
  would spare the reader the §8 round-trip; natural next-repair/fold
  item.
* (q4) Standing: blueprint/completion-tree cites commit-unpinned
  (motion-free re-verified at HEAD: 00ce2b6/46e583e; PE5 m3/PE6 p2);
  §5's GRB dated-REV cite (PE4 n1; record still at 7598491); §7.3's
  short-form `[r5]` bracket (r2-precedent convention, PE6 p1).
* (q5) The matrix probe is /tmp-only, disclosed uncommitted (md5
  `8fd286d0`); available for sealing alongside the PE6 Lean leg if the
  arc wants a second committed fresh-leg artifact.

**What survived this hostile pass (for the record):** the r5 diff
faithful at every edit site with BOTH as-of quotes byte-exact at
`git show 94534df` (whitespace-normalized mechanical compare) and every
timeline fact exact against git (79d1d9c 09:31:14 / debf99d 09:46:49 /
a48c22d 09:44:33 / 94534df 14:20:00 / f131c53 14:47:46); the [JA-r5]
blast-radius claims independently re-verified three ways (pin present;
§6.3 byte-identical ffa1e57 == 79d1d9c, own diff; the sole later §6.3
motion = the forward-only weakening the bracket quotes; no JA
derivation rides the converse, own read); the arc system true at every
live surface with the ledger line "JA 0/2 (PE7 = attempt)" and all
eleven round facts exact against git; the machine bracket bit-identical
(exit 0, 17 families, 10,311/0, boundary 16 = 9+7, bpref 26 = 22-on-10
+ 4, elapsed 5.4 s) with seals intact at pins and worktree and every
census recounted from the committed JSON; the entire §3/§4 exponent
system re-derived by the unimodular-matrix route — master lemma from
change-of-basis, the ε-exponent as the lattice T-coordinate, covariance
from one lattice vector, BOTH orbit displays as the single row-operation
identity T ↦ T − κV, the carry as group-algebra exponent overflow —
confirmed by an engine-free, pool-free probe with a third Bézout
technology: 322,916 checks, 0 violations; all four theorem displays
statement-level true at HEAD with their fences.

JA-PE7 FINDINGS: 0 critical, 0 justification gaps, 0 minor
VERDICT: CLEAN — the first clean pass at the post-PE4-reset counter
(counter advance 0/2 → 1/2 is the orchestrator's ledger action); the
next pass is the would-be accepting attempt. Observations q1–q3 name
the exact brackets any future repair round owes before it re-arms the
fired-trigger species.
