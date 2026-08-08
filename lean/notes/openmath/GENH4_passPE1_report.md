# GENH4 passPE1 report — hostile verification of GENH4_PROOF_2026-08-08.md

**Verifier:** fresh-context hostile pass PE1 (full complete-theorem bar).
**Target:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` at HEAD (970022b);
arc skeleton ea5978d → seal 121d9ab → verdict run-1 RED 3eb1667 → verdict
run-2 GREEN 4b5c085. **Charges:** (1) RED→GREEN forensics, (2) GENH4-4 carry
bijection re-derivation, (3) GENH4.A vs the committed QSCOUT22 table + the L3
512-vs-256 correction, (4) GENH4-6 P-D unreachability, (5) the eleven R_τ(q),
(6) the S11 conditionality stack; machine re-run; fresh-route own arithmetic.

**STATUS: IN PROGRESS (skeleton commit; findings and verdict below are
partial until the final section says COMPLETE).**

---

## Charge 1 — THE RED→GREEN ARC (forensic audit): CLEAN

Verified from git objects and committed artifacts, not from the note's prose:

* **The repair touched ONLY the generator.** `git diff 121d9ab..3eb1667 --
  verification/openmath/genh4_checks.py` is EXACTLY one functional line inside
  `run_feven` — `Q.elems_with_floor(R, f0dv - k)` → `(R, f0dv - k + 1)` — plus
  a 3-line comment. No law code (`law_E`/`law_F`), no checker, no other row.
  `git diff 3eb1667..4b5c085` on the runner is EMPTY (commit 3 added only the
  run-2 artifacts + note §S13.2). `git diff 4b5c085..HEAD` on runner +
  artifacts + note is EMPTY (no post-verdict motion).
* **The diagnosis is what actually happened.** Run-1 artifacts (committed at
  3eb1667): exactly ONE violation line —
  `[GH-FEVEN] ... ('F', (), 1, (), 'RAM', (5,)): obs 3188646 exp 0`, row
  members 4,782,969 = 3¹⁴ = 3 × the sealed prediction 3¹³ = 1,594,323. My own
  recount of the mis-floored box {v(α₁)≥2, v(α₀)≥3, v(β₁)≥4, v(β₀)≥6} at
  (q,N,k) = (3,7,1): 13 free digits × 3 ψ-choices = 3¹⁴ ✓; the leaked key =
  {v(β₁) = 4 exactly} → v₁(A₀) = 5 attained by the β₁ component alone → RAM(5),
  count per ψ = (q−1)·q³·q⁹ (freed digit × A₀ slots above 5 × all 9 A₁ digits;
  RAM condition u ≤ 2w automatic since w ≥ 3), × 3 ψ = 3,188,646 — the
  observed count ON THE NOSE. The other 8 keys of the run-1 row are
  byte-identical to the run-2 (repaired) row — as they must be: keys with
  dv0 ≥ 6 are insensitive to the β₁ floor 4-vs-5 (their loci sit inside both
  boxes); I confirmed key-by-key from the two committed JSONs.
* **The sealed prediction pre-dates the repair.** `git show
  121d9ab:...GENH4_PROOF...md` lines 892–893 contain P-3's
  "GH-FEVEN (Zp,3,7,k1,f0=5): 3·3¹² = 1,594,323 members, 8 keys incl.
  F-SPLITEQ(3)/INERT(3) at the F₉ censuses 28/36" — sealed BEFORE run 1. The
  repaired run delivered exactly 1,594,323 members / 8 keys, with
  SPLITEQ(3) = 551,124 = 28·3⁹ and INERT(3) = 708,588 = 36·3⁹ (F₉ censuses
  live at odd q, as predicted).
* **No law-side motion between runs.** Full leaf-diff of
  `genh4_checks_results_run1.json` vs `genh4_checks_results.json`: exactly 3
  non-timing leaf diffs — the FEVEN row, the GH-FEVEN family line (9,1 →
  8,0), the verdict RED→GREEN. Every other row/family/tooth/R_τ leaf is
  byte-identical.
* **Note-text motion between seal and verdicts is exactly the disclosed set.**
  Seal→commit-2 diff on the note: §S13.1 + the flagged "[commit-2 display
  addition]" E[#roots] spot identity in S9.4b + the S13 header. Commit-2→3:
  §S13.2 only (replacing the placeholder). No sealed statement touched.
* **Timeline consistency (single-run honesty).** Seal 11:45:04 → commit-2
  12:06:42 = 21m38s vs run-1's logged 1,102.2 s (18.4 m); commit-2 → commit-3
  12:23:51 = 17m09s vs run-2's logged 947.5 s (15.8 m). Both windows fit
  exactly one fresh run + a short diagnosis/append — no room for hidden
  reruns.
* **Pins.** At HEAD: runner md5 ee8024b7… (= S13.2's claim), output
  9e6ca9b3…, results cbcff562… ✓; seal-time runner e5e435c3… ≠ repaired
  ee8024b7… (one line); qscout22 runner cb885663…, results 6c2441a…, w10
  a9c34244, w12 7dc040d9, engine 7240a916 — all six GH-PIN targets match the
  note's pins at HEAD.

**Charge-1 verdict: the RED→GREEN arc is forensically clean.** The RED was
genuinely instrument-side, quantitatively diagnosed correctly, the repair is
minimal and generator-only, the sealed predictions were correct pre-repair.

## Charge 3 — GENH4.A vs the committed QSCOUT22 table: VERIFIED (own recounts)

All from `qscout22_results.json` (md5 6c2441a… ✓) read directly, counts
re-derived by my own slot-string arithmetic from S2.3/S6.1 (no runner code):

1. **The L3 correction row (2,7,3):** committed row `consE Zp q=2 N=7 h=3` has
   exactly 2 keys: RAM(13) = 512, UND = 512. The scout's quoted law
   (q−1)q^{N+(h−1)/2} = 2⁸ = 256 is REFUTED by the committed artifact; the
   note's corrected law (q−1)q^{N+h−1} = 2⁹ = 512 MATCHES. My derivation:
   budgets at (h,N) = (3,7): β₁ slots dv ∈ {13,15}, β₀ slots EMPTY
   ([2h+1,N−1] = [7,6]), α₁ slots {7,9,11,13,15}, α₀ slots {8,10,12} — 10
   slots = 4N−5h−3 ✓ (row total 2¹⁰ = 1024 ✓). UND = A₀-readable-zero: slot
   13 pinned 0, band slot 15 free, all 8 A₁ slots free → 2⁹ = 512 ✓. Also
   RAM(13) = (q−1)·2^{1+8} = 512 ✓. Coherence: no SPLTAIL key possible here
   (w ≥ 2h+1 = 7 = N), matching the 2-key row.
2. **F even-N two-term UND law:** `consF Zp q=2 N=8 k=1` UND = 1024 =
   q^{2⌊N/2⌋+2k−1} + (q−1)q^{N+2k−1} = 512 + 512 ✓.
3. **F-RAM(5) same row** = 196,608 = (q²−1)·2^{16}: my slot count — A₀
   pair-slots above 5: m ∈ {6,7} comp 2 + m = 8 comp 1 → 5; A₁: m ∈ [3,8]
   all with 2m > 5 → comp 11; census Q−1 = 3 → 3·2^{16} ✓.
4. **F-INERT(3) same row** = 24,576 = Q(Q−1)/2 · 2^{3+9} = 6·4096 ✓ (A₀ slot
   m=5 between floor and 2dμ = 6 pinned zero; A₀ > 6 comp 3; A₁ > 3 comp 9).
5. **E history-resolved key** `consE Zp q=3 N=5 h=1`, H₂ = (3), RAM(7) =
   52,488 = (q−1)_{entry}·L_E^{t=1}·(q−1)_{census}·q^{2+6} = 2·2·2·3⁸ ✓
   (post-refine floor {dv(A₁) > 3, dv(A₀) > 6}; A₀ free slots above 7 =
   {8,9}; A₁ free slots {4,…,9}, all with 2s > 7).
6. **Fresh q=7 row (P-3, never measured):** consE (Zp,7,3,h1): my own budget
   arithmetic gives total (q−1)q⁴ = 14,406, RAM(5) = 6·6·7³ = 12,348,
   UND = 6·7³ = 2,058 — exactly the committed run values and the sealed P-3.

**Charge-3 verdict: GENH4.A's law and the GENH4.B correction verified against
the committed artifact by independent arithmetic.**

## Charge 2 — GENH4-4 (the carry bijection) — IN PROGRESS

(to be filled: own exact-arithmetic instance computations, E odd-dμ carry +
twist-kill and F pair-kill, exactness beyond the window)

## Charge 4 — GENH4-6 (P-D unreachability) — IN PROGRESS

## Charge 5 — the eleven R_τ(q) — IN PROGRESS

## Charge 6 — S11 conditionality stack — IN PROGRESS

## Machine leg — full fresh re-run — RUNNING

## Fresh route — own-arithmetic composite rows — IN PROGRESS

## FINDINGS (running list)

(none confirmed yet)
