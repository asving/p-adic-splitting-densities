# O4T — the O-4 drainage transfer — Phase-B attempt record, REV 4 (Fable, 2026-08-02)

Light-repair round after the pass-3 hostile audit (the first acceptance-grade pass).
This record is a DELTA on `O4T_phaseB_attempt_rev2.md` (still the full unit record —
what was achieved, the falsifier record, the design decisions) and
`O4T_phaseB_attempt_rev3.md`; only the pass-3 dispositions and the file map change.

## 1. What happened

Pass 3 (`O4T_pass3_verify.md`; Fable, fresh context, standalone read of
`O4T_phaseB_verifybrief_rev3.md` only, full clean-pass charge including all 11 §7
attack items) returned **SOUND-WITH-GAPS — zero critical errors, two minor
justification gaps**, "both localized to single sentences whose surrounding
conclusions are true and independently re-derivable". The ENTIRE mathematical core was
upheld line-by-line, all 11 §7 charges PASS, and the harness was re-run in full (all
five exhaustive configs, 2,534,851 classes, ALL PASS; the regenerated JSON is
byte-identical to the sealed `O4T_transfer_results.json` modulo the five timing
fields). Per the adjudication (commit 7b28562: "O4T one confirming pass away"), rev 4
executes the two single-sentence repairs and puts the pass-3 observation on record.

## 2. Pass-3 findings → rev-4 dispositions (full table = rev-4 brief §0-pre-4)

1. **GAP-1 (minor) — (I1)'s step-0 proof sentence false as written.** "Reducing to `r`
   ⟺ `v(α − r) ≥ 1`" fails: root differences take FRACTIONAL valuations in (0, 1)
   (verifier's refutation `f = x² − p`: both roots `±√p` reduce to 0 with `v = 1/2`).
   REPAIRED: the criterion is corrected to `> 0`, with the verifier's one-line
   derivation (`ᾱ = r ⟺ α − r ∈ 𝔪 ⟺ v(α − r) > 0`) displayed, and a note pinning
   that nothing downstream consumes the retired `≥ 1` form (the case (a)/(b)
   arithmetic uses `b_2 > λ_prev` only).
2. **GAP-2 (minor, prose) — "I-TAIL remains the one EXTERNAL named import"
   undercounts.** M05 Lemma B (separable lifts exist — what makes `c^sem` a
   well-defined function; consumed by FLOOR) and M05 Lemma D (Krasner–Hensel local
   constancy — `c^K`'s soundness; NOT the (K) identity the terminal clause consumes)
   are also external displayed imports. REPAIRED: the §3.1 closing sentence replaced
   by a THREE-import count (I-TAIL + M05 Lemmas B/D), each with its exact, limited
   consumption sites, plus the §3-proofs-only scoping under which I-TAIL is the only
   one.
3. **Observation (not a finding) — (C1) is logically REDUNDANT** (every hull-defining
   resolved point has height < k, so (C1) can never fail; the certificate's operative
   gate is `x₀ ≤ 1` + (C2)). RECORDED as a rev-4 note after the §3.2 walk so no future
   reader credits (C1) with gating work it does not do; the pinned policy itself is
   UNCHANGED — no normative content moved, (CEIL) stays stated/proved/tested for the
   displayed walk.

Everything pass 3 upheld is byte-stable (diff-verified: 9 hunks, all at the named
repair sites + title/changelog/status/ledger/charges). New §7 charge 12 hands the
confirming pass the rev-4 repairs as explicit attack targets.

## 3. Honest status

**PROVED-UNVERIFIED at rev 4 — one confirming clean pass from acceptance** (rev 1
UNSOUND at V30, TR-Q critical; rev 2 UNSOUND at pass 2, N3-BRACKET terminal `=`; rev 3
SOUND-WITH-GAPS at pass 3 — zero criticals, full core and all 11 charges upheld).
TR-OM remains CONDITIONAL-OPEN on (AGR) exactly as before. NUM (P1–P6, 2,534,851
classes, ALL PASS) untouched — no harness or numeric change in this round; no Lean
edits.

## 4. Files (delta)

* `lean/notes/openmath/O4T_phaseB_verifybrief_rev4.md` — the repaired self-contained
  brief (REV 4 — hand THIS to the confirming pass; §0-pre-4 = the pass-3 disposition
  table; priority charges = §7 item 12).
* `lean/notes/openmath/O4T_phaseB_attempt_rev4.md` — this record.
* `lean/notes/openmath/O4T_pass3_verify.md` — the pass-3 audit rev 4 repairs.
* Superseded (kept byte-stable as history): the rev-3 pair, the rev-2 pair, the rev-1
  pair, `V30_o4t.jsonl`, `O4T_pass2_fable_verify.md`.
* Unchanged: `verification/openmath/O4T_transfer_check.py` + sealed results/logs.
