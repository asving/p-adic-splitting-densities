# GENH4 passPE1 report — hostile verification of GENH4_PROOF_2026-08-08.md

**Verifier:** fresh-context hostile pass PE1 (full complete-theorem bar; quote-
and-classify; fixes nothing). **Target:** `lean/notes/openmath/
GENH4_PROOF_2026-08-08.md` at HEAD (970022b); arc skeleton ea5978d → seal
121d9ab → verdict run-1 RED 3eb1667 → verdict run-2 GREEN 4b5c085.
**Charges:** (1) RED→GREEN forensics, (2) GENH4-4 carry-bijection instances,
(3) GENH4.A vs the committed QSCOUT22 table incl. the L3 512-vs-256
correction, (4) GENH4-6 P-D unreachability, (5) the eleven R_τ(q), (6) the
S11 conditionality stack; machine re-run; fresh-route own arithmetic.

## VERDICT: NOT CLEAN — 0 CRITICAL + 0 GAPS + 1 MINOR (+2 remarks).

Every theorem-level claim audited survives; the RED→GREEN arc is forensically
clean; the machine leg reproduces bit-identically; the fresh route confirms
three rows key-for-key and the density display by two independent symbolic
routes. The one minor is a stale supplier-status cell in the grade box.

### FINDINGS

* **MINOR (S10-BOX-1, display-accuracy):** the grade-box cell "HMENU3 (0/2,
  PE2 next)" was stale already at compose time: HMENU3 passPE2 landed
  af988ee 10:32:56 and its r2 e1280be 11:05:02, BEFORE the skeleton ea5978d
  11:05:32 (the phrase is present at ea5978d line 671) and 40 min before the
  seal. Correct display was "(0/2, r2, PE3 next)". Grade 0/2 and "arcs live"
  remain true; no conditionality change — in fact HMENU3 passPE3 CLEAN
  (7e5026a 11:55) landed between seal and verdict, STRENGTHENING the stack.
  One-word repair owed.
* **REMARK 1 (supplier aging inside the verdict window, not a finding):**
  HEX3 passPE2 (f60348b 11:47:39, 0C+1G+1m) landed 2.5 min AFTER the GENH4
  seal, and HEX3 r2 (a707430) landed between GENH4 commits 2 and 3; the note
  pins HEX3 @ r1 2580f12. Pins are declared "as-of"; HEX3-PE2 found no
  critical and nothing GENH4 consumes (ν₃/P(3) conclusions untouched — the
  PE2 findings concern HEX3's own never-measured census bookkeeping and an
  S8.2 aside). A verdict-time supplier-arc refresh (as HMENU3 r2 practiced)
  would have caught both this and the MINOR above.
* **REMARK 2 (S13.1 notation):** "obs = 3,188,646 = 3ψ·(q−1)·q³·q⁹" reads
  only if "3ψ" means "the 3 choices of ψ" (the F₉ irreducible-quadratic
  census (q²−q)/2 = 3), i.e. obs = 3·(q−1)·q¹². The number is exactly right;
  the notation is ambiguous (could parse as 3·ψ·(q−1)q¹² = 9,565,938).

---

## Charge 1 — THE RED→GREEN ARC (forensic audit): CLEAN

Verified from git objects and committed artifacts, not from the note's prose:

* **The repair touched ONLY the generator.** `git diff 121d9ab..3eb1667 --
  verification/openmath/genh4_checks.py` is EXACTLY one functional line inside
  `run_feven` — `Q.elems_with_floor(R, f0dv - k)` → `(R, f0dv - k + 1)` — plus
  a 3-line comment. No law code (`law_E`/`law_F` untouched), no checker, no
  other row. `git diff 3eb1667..4b5c085` on the runner is EMPTY (commit 3
  added only run-2 artifacts + note §S13.2). `git diff 4b5c085..HEAD` on
  runner + artifacts + note is EMPTY (no post-verdict motion). Also checked:
  the runner never calls the qscout22 MODEL functions (its `law_E`/`law_F`
  are its own; only the pinned reader `read22` is imported, as disclosed).
* **The diagnosis is what actually happened.** Run-1 artifacts (committed at
  3eb1667): exactly ONE violation line —
  `[GH-FEVEN] ... ('F', (), 1, (), 'RAM', (5,)): obs 3188646 exp 0`, row
  members 4,782,969 = 3¹⁴ = 3 × the sealed prediction 3¹³ = 1,594,323. My own
  recount of the mis-floored box {v(α₁)≥2, v(α₀)≥3, v(β₁)≥4, v(β₀)≥6} at
  (q,N,k) = (3,7,1): 13 free digits × 3 ψ-choices = 3¹⁴ ✓; the leaked key =
  {v(β₁) = 4 exactly} → v₁(A₀) = 5 attained by the β₁ component alone →
  RAM(5), count per ψ = (q−1)·q³·q⁹ (freed digit × A₀ slots above 5 × all 9
  A₁ digits; RAM condition u ≤ 2w automatic since w ≥ 3), × 3 ψ = 3,188,646 —
  the observed count ON THE NOSE. The other 8 keys of the run-1 row are
  byte-identical to the run-2 (repaired) row, as they must be (dv0 ≥ 6 keys
  are insensitive to the β₁ floor 4-vs-5); confirmed key-by-key from the two
  committed JSONs.
* **The sealed prediction pre-dates the repair.** `git show 121d9ab:…md`
  lines 892–893 contain P-3's "GH-FEVEN (Zp,3,7,k1,f0=5): 3·3¹² = 1,594,323
  members, 8 keys incl. F-SPLITEQ(3)/INERT(3) at the F₉ censuses 28/36" —
  sealed BEFORE run 1. The repaired run delivered exactly 1,594,323 members /
  8 keys, with SPLITEQ(3) = 551,124 = 28·3⁹ and INERT(3) = 708,588 = 36·3⁹
  (F₉ censuses live at odd q, as predicted; refine letters 8 = q²−1).
* **No law-side motion between runs.** Full leaf-diff of run-1 vs run-2
  results JSONs: exactly 3 non-timing leaf diffs — the FEVEN row, the
  GH-FEVEN family line (9,1 → 8,0), verdict RED→GREEN. Every other
  row/family/tooth/R_τ leaf byte-identical.
* **Note-text motion between seal and verdicts = exactly the disclosed set.**
  Seal→commit-2: §S13.1 + the flagged "[commit-2 display addition]" E[#roots]
  spot identity in S9.4b + the S13 header. Commit-2→3: §S13.2 replacing the
  placeholder (only removed lines = the placeholder). No sealed statement
  touched.
* **Timeline consistency (single-run honesty).** Seal 11:45:04 → commit-2
  12:06:42 = 21m38s vs run-1's logged 1,102.2 s; commit-2 → commit-3 12:23:51
  = 17m09s vs run-2's logged 947.5 s. Both windows fit exactly one fresh run
  + a short diagnosis/append — no room for hidden reruns.
* **Pins.** At HEAD: runner md5 ee8024b7… (= S13.2's claim), output
  9e6ca9b3…, results cbcff562…; seal-time runner e5e435c3… ≠ repaired
  ee8024b7… (the one line); qscout22 runner cb885663…, results 6c2441a…, w10
  a9c34244, w12 7dc040d9, engine 7240a916 (at `verification/
  om_density_engine.py`) — all GH-PIN targets match at HEAD.

## Charge 2 — LEMMA GENH4-4 (the carry bijection): VERIFIED, EXACT

Own instance computations (`/tmp` scripts, reproduced in this report's
record): I build f = φ² + A₁φ + A₀ from a '1sq' state, recenter φ′ = φ − ŝn₂,
and recompute the development by RAW POLYNOMIAL DIVISION — in **exact ℤ**
(mixed char, π = p) and **exact F_q[t]** (equal char). No window truncation
exists in these rings, so a passing kill is EXACT by construction, not
approximate-mod-window.

* **E, q = 3, z = 2 (nontrivial twist), h = 1, dμ = 3 (odd — the carry
  case), s = 2:** with the twisted '1sq' data (digit₁(α₁) = −2s = 2,
  digit₃(β₀) = z·s² = 2), division gives A₁′ = 27x+189, A₀′ = 1161x+891:
  dv(A₁′) = 6 > 3, dv(A₀′) = 7 > 6 — both pins DEAD, the 2dμ-digit exactly
  zero (v₃(891) = 4). The note's closed formulas check against the raw
  division: A₁+2w+C = 27x+189 ✓ (C = ŝ²π² + α₁ŝπ = 126, even parity, landing
  at heights > dμ), A₀+λ−C(p₁′x+p₀′) = 1161x+891 ✓.
* **UNTWISTED CONTROL (same state but digit₃(β₀) = s² = 1, the untwisted
  reading):** the kill FAILS — dv(A₀′) = 6, the 2dμ-digit survives. The
  z̄-twist cancellation (S₀ + zs² − 2zs² = 0) is genuinely load-bearing and
  exact; a wrong twist convention is instantly visible.
* **E, mixed char 2 (p = q = 2, s = 1):** kill exact (S₀ + zs² = 2zs², v ≥ 1
  in ℤ₂) — dv(A₀′) = 7 > 6.
* **E, deeper dμ = 5:** kill exact.
* **F, q = 3, k = 1, ψ = y²+1 (c₁ = 0) and ψ = y²+y+2 (c₁ ≠ 0, the wrap
  through the ψ-relation live), letters S = ȳ+1 and S = ȳ:** pair-kills
  exact (v₁(A₁′) = 4 > 3, v₁(A₀′) = 7 > 6); a wrong-S₀-pair control FAILS.
* **Equal characteristic:** F₃[t] twisted instance + untwisted control
  (same verdicts), and F₂[t] instances at (h,dμ) = (1,3) and (3,7) — in
  equal char 2, 2w = 0 identically and the kill still lands via
  S₀ + zs² = 2zs² = 0; at (3,7) the carry C = ŝ²t⁴ is visibly the only
  A₁-revival term.

Additionally the fresh-route walkers below re-enter the floored node after
EVERY refine event with floor-assertions armed (E row: ~10⁵ refine events
across 1.06M members; F row: 768 events) — zero assertion failures: a mass
pointwise confirmation of the bijection's image claim by independent code.

## Charge 3 — THEOREM GENH4.A/B vs the committed QSCOUT22 table: VERIFIED

All from `qscout22_results.json` (md5 6c2441a… ✓) read directly; counts
re-derived by my own slot-string arithmetic from S2.3/S6.1 (no runner code):

1. **The L3 correction row (2,7,3):** committed row `consE Zp q=2 N=7 h=3`
   has exactly 2 keys: RAM(13) = 512, UND = 512. The scout's quoted law
   (q−1)q^{N+(h−1)/2} = 256 is REFUTED by the committed artifact; the note's
   corrected law (q−1)q^{N+h−1} = 2⁹ = 512 MATCHES. My derivation: budgets at
   (h,N) = (3,7): β₁ slots dv ∈ {13,15}, β₀ slots EMPTY ([7,6]), α₁ slots
   {7,9,11,13,15}, α₀ slots {8,10,12} — 10 slots = 4N−5h−3 (row total 2¹⁰ ✓).
   UND = slot-13 pinned 0 × band slot 15 free × all 8 A₁ slots free = 2⁹ ✓;
   RAM(13) = (q−1)·2^{1+8} = 512 ✓. Coherence: no SPLTAIL key possible here
   (w ≥ 2h+1 = 7 = N), matching the 2-key row.
2. **F even-N two-term UND law:** `consF Zp q=2 N=8 k=1` UND = 1024 =
   q^{2⌊N/2⌋+2k−1} + (q−1)q^{N+2k−1} = 512 + 512 ✓; odd-N single power:
   (2,7,1) UND = 2⁷ = 128 ✓, (2,9,2) UND = 2¹¹ = 2048 ✓, fresh (7,5,1)
   UND = 21·7⁵ = 352,947 ✓.
3. **F-RAM(5) at (2,8,1)** = 196,608 = (q²−1)·2^{16} (comp-weighted slots:
   A₀ above 5 = 5, A₁ with 2m > 5 = 11) ✓.
4. **F-INERT(3) at (2,8,1)** = 24,576 = Q(Q−1)/2·2^{3+9} = 6·4096 ✓.
5. **E history-resolved key (3,5,1), H₂ = (3), RAM(7)** = 52,488 =
   (q−1)_{entry}·L_E·(q−1)_{census}·q^{2+6} = 2·2·2·3⁸ ✓.
6. **E UND aggregate law (GENH4.B):** (3,5,1): Σ_{H₂} UND = 486+972+972+1944
   = 4,374 = (q−1)^{r+1}q^{2N−h−2} = 2·3⁷ ✓; bracket telescoping visible in
   the RAM(9) family: 972/1944/1944/3888 over H₂ = ∅,(3),(4),(3,4), summing
   to 972·q^δ with δ = 2 ✓ (S6.2's CS-2 bracket, exact).
7. **Fresh q = 7 row (P-3, never measured):** consE (Zp,7,3,h1): own budget
   arithmetic gives total (q−1)q⁴ = 14,406, RAM(5) = 12,348, UND = 2,058 —
   exactly the sealed P-3 and the battery values.

## Charge 4 — GENH4-6 (P-D settled): VERIFIED

* **Liveness re-derivation (own algebra).** Readable refine depths: E:
  2h+1 ≤ dμ ≤ N−1 (cap 2dμ < 2N; floor > 2h). Odd dμ: S₁ position (dμ−h)/2 ≥
  (h+1)/2 (from dμ ≥ 2h+1, exact at the boundary) and ≤ N−1 (from dμ ≤ N−1 ≤
  2N−2+h). Even dμ: position dμ/2 ∈ [h+1, N−1] (from dμ ≥ 2h+2 even and
  dμ ≤ N−1). F: 2k+1 ≤ dμ ≤ ⌈N/2⌉−1: a₀-position dμ ≤ N−1, a₁-position
  dμ−k ∈ [k+1, N−1]. All four chains close — the S₁ slot is live at every
  reachable refine event; strings key-independent and floors only rise, so
  this covers all histories/prehistories. With the slot live, '1sq' = Q−1
  pairs of the Q(Q−1) unit-pairs in BOTH characteristics (odd: s ↦ (−2s,
  z·s²); char 2: (0, S₀), S₀ ∈ K^× — same count), rate 1/Q. P-D's dead-slot
  cascade is therefore unrealizable at the n = 4 stages: a theorem. ✓
* **The two smoke-caught weakenings are the proved forms.** On {A₁ ≡ 0}: an
  even-dμ refine adds only 2w (deg-0, C = 0) — equal char 2 keeps A₁ ≡ 0, so
  along all-even H₂ every read has S₁ = 0 → '1sq' forced (the cascade); but
  (i) mixed char 2 revives A₁ via 2w ≠ 0, and (ii) equal char 2 revives A₁
  at any ODD dμ via the carry C = ŝ²π^{dμ−h} (my equal-char-2 instances show
  exactly this term). So the honest statement is precisely the note's: cascade
  forced exactly along the carry-free all-even ladder — matching the machine
  record (Fqt q=2 cascade row: all-even-H₂ leaves are RAM/UND only; Zp q=3
  row realizes SPLITEQ and INERT at all-even H₂ — the separator).

## Charge 5 — THE ELEVEN R_τ(q): VERIFIED (three routes, two of them mine)

* **Σ_τ R_τ = 1 SYMBOLIC** on the eleven displayed forms (typed from the note
  by hand into sympy): exact identity in ℚ(q). All 22 anchors (q = 2, 3)
  match the display exactly.
* **E[#roots]:** Σ_τ #{(1,1) parts}·R_τ = q/(q+1) — verified SYMBOLICALLY
  (stronger than the note's anchors-only claim).
* **Own level-0 assembly × engine blocks (decorrelated route):** my own
  shape censuses over F_q (Σ = q⁴ verified symbolically: C(q,4), C(q,2)n₂,
  C(n₂,2), qn₃, n₄, qC(q−1,2), qn₂, C(q,2), q(q−1), q, n₂) convolved with the
  md5-pinned engine's cluster laws β₂, β₃, β₄, β₂-scaled(2) (derived by the
  engine's own Igusa-cell fixpoint — a route independent of this note's
  polygon assembly AND of the runner's `nu4_families`): **reproduces ALL
  ELEVEN displayed R_τ symbolically**, with no extra types. This
  simultaneously verifies ν₄ ≡ β₄ / ν₃ ≡ β₃ / ν₂ ≡ β₂ at the level the
  display consumes them, at symbolic q (hence a fortiori at q = 2, 3:
  ν₄(4,1) = 856/1533, 27081/39364 — engine and my polygon route agree
  exactly).
* **Own Newton-polygon derivation of R_{(4,1)} (fully independent):** masses
  m_RAM4 = Σ_{u odd}(1−t)t^{Σ⌈·⌉} = (1−t)/(1−t⁵), m_G2 = (1−t)t²/(1−t^{10}),
  m_loop = (1−t)t⁹/(1−t^{10}) (t = 1/q; my own ⌈u(4−j)/4⌉ bookkeeping —
  m_loop matches the note's Σ(q−1)q^{−10k}); '1sq' fraction 1/q; μ_E(4,1) =
  q/(q+1) (W-11, accepted supplier); fixpoint ν₄(4,1) = (m_RAM4 +
  m_G2·q^{−1}·q/(q+1))/(1 − m_loop); then R_{(4,1)} = ν₄(4,1)/q³ =
  (q⁶+q⁵+q³+q+1)/((q+1)Φ₂Φ₃) — EQUALS the display symbolically, and equals
  the engine's β₄({(4,1)})/q³.
* **Finite-window sandwiches (own arithmetic):** τ = (4,1) on committed full
  rows (Zp,2,5), (Zp,2,6), (Zp,3,4): my own resolved/unresolved key
  classification gives resolved ≤ ν₄(4,1)·q^{4(N−1)} ≤ resolved+unresolved as
  exact rationals — OK ×3 (e.g. (2,6): 585,216 ≤ 897,581,056/1533 ≈ 585,506.2
  ≤ 620,288).

## Charge 6 — S11 conditionality stack: VERIFIED (with the MINOR above)

All 18 pinned commits exist and their subjects match their claimed roles
(GENIND 4682bcf/4984004; QSCOUT22 dd67cda/970197d; W-12 f669cb0/99f1813; W-11
7020ceb/31506b3 + PE3 839b735 + PE4 16d12e1 = accepted 2/2 ✓ before the seal;
HEX3 e3f3459/671a126/2580f12; HMENU3 64d3ff9/625fa49; GRTJC 83f47f4; J-D0
9387eb1; DULEMMA f819f26; engine md5 7240a916 ✓). Grade-box accuracy at seal:
W-11 2/2 ✓, W-12 "PE3 owed" ✓, HEX3 "r1" ✓ (PE2 landed 2.5 min after seal —
Remark 1), GENIND "unopened" ✓, HMENU3 cell stale (the MINOR). Surface-claim
audit: every P(4)/discharge statement (title, S9.1, S13.2, GENH4-BOX-1)
carries "conditional exactly on the S11 arc-grade stack"; P(5) explicitly NOT
claimed (BOX-2); the general (H-e) explicitly open; the density engine
scoped as corroboration only (BOX-6); the tame/weld seams explicitly not
consumed (S0 division, checked against S3/S5's elementary re-proofs — the
count laws use only parity/independence facts proved in the note). Nothing
claims more than the discharge + the displayed stack warrants.

## Machine leg: GREEN, bit-identical

Full fresh re-run of the HEAD runner in an isolated copy (so committed
artifacts stay untouched): **exit 0, GREEN, 941.4 s**, family totals
6/481/54/5/192,000/8/46,590/92/157/115/6,185 all with 0 violations
(= 245,693 checks), teeth LAT 19 / CEN 14 / ALPH 4 / SIG 2 / DENS 1 — every
count identical to S13.2 and the committed artifacts; output txt identical
ex-timing; results JSON has ZERO non-timing leaf diffs vs the committed
`genh4_checks_results.json`.

## Fresh route (own arithmetic, no runner imports)

Three composite rows re-derived with my own code (own polynomial division,
own digit reads, own residual classification, own F₄ arithmetic, own
twist/carry handling) — plus one row fully by hand:

* **consE (Zp,7,3,h1) [never-measured, q = 7]:** FULL SCAN of all 5,764,801
  coefficient tuples (πO/π³)⁴ — the E(1)-'1sq' locus emerges with exactly
  14,406 members and keys RAM(5) = 12,348 / UND = 2,058 = sealed P-3 = the
  battery. (Tests the entry fibration too: no other member of the 5.76M
  space enters.)
* **consF (Zp,2,7,k1) [committed, 9 keys]:** by-hand derivation of all nine
  key counts from the note's laws (12,288 = 3·2¹²; SPLITEQ/INERT = 3/6·2⁸;
  refine → RAM(7)/UND = 384/384; band RAM(7) = 128; 2SIDED(3,4) = 384;
  SPLTAIL 384; UND 128; total 16,384) AND own-walker enumeration of the
  16,384-member locus with F₄ pair-reads and refine recursion — all 9 keys
  match the committed JSON exactly. Also decodes the key grammar: 2SIDED
  params = (w, u−w) with u = N attained via the comp-1 boundary band, exactly
  as GENH4-CAP(F) prescribes.
* **consE (Zp,3,5,h1) [committed, 25 keys, histories to depth 2]:** own
  walker with the z̄-twist at odd dμ, both refine parities (the odd-dμ CARRY
  path live), and floor-assertions armed — all 25 keys match the committed
  row exactly over 1,062,882 members; zero floor violations.

## Scope not re-proved here (for the record)

THEOREM GENH4.C's five σ-cases were re-derived at reading depth (norm/
j = 2 argument, parity-of-valuation e-forcing, residue-field f-forcing,
SPLITEQ-via-one-refine, SPLTAIL undercut) and are machine-tied by 6,185 PARI
checks incl. 4,130 q = 7 members; I did not run an independent σ oracle
beyond the battery's. GENH4.A's general X-exponent affine forms were checked
at the 7 spot keys + 3 whole rows above, not re-derived leaf-family by
leaf-family at symbolic (N,h,k).

**Counter: this is pass PE1 → NOT CLEAN (1 minor) → repair (r1) then PE2.**
