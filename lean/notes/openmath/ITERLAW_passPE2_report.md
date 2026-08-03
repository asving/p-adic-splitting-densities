# ITERLAW-PE2 — Fable hostile pass 2 (execution + content) on the AMENDED ITER-LAW note (post-errata 7566ccd)

```
FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
```

Fresh verifier (no prior-report trust; arc consumed as history only). Target:
`lean/notes/openmath/ITERLAW_2026-08-08.md` at HEAD (= errata commit 7566ccd
content), the sealed falsifier `verification/openmath/iterlaw_check.py` (seal
ab7c31c), the errata supplement `verification/openmath/iterlaw_cor4_mixed.py`,
and the PE1 F2c reimplementation `verification/openmath/iterlaw_f2c_reimpl.py`.
Charge: errata fidelity, seal integrity, supplement hostile read, three re-runs,
fresh content read, quote-and-classify, fix nothing. All target files READ-ONLY;
nothing outside this report + the ledger entry was written.

## 1. Errata fidelity (charge 1) — PASS

**Bracket additivity.** `git diff 242ba1e..7566ccd -- lean/notes/openmath/
ITERLAW_2026-08-08.md` = +49/−1 lines in exactly four hunks (S0, S6.4, S8, S9).
The single deleted line is NOT a substantive deletion: the S9 bullet line
`  (general-lift extension (ITER-LAW-LIFT) open; orders ≥ 3 open). §S3's binding`
was split to insert the ERRATUM CROSS-REF bracket mid-line; both fragments
(`... orders ≥ 3 open).` before the bracket, `§S3's binding` after `]**`)
survive verbatim, so concatenation reproduces the original character-for-
character. **Bracket-fidelity verdict: insertions-only in substance — YES**
(zero substantive lines deleted; original struck bracket-style, not removed).

**Proof sections untouched.** S2–S5 have zero changed lines. S6 has zero
modified or deleted lines; the only S6 change is the purely-additive SUPPLEMENT
BRACKET appended after the COR-4 paragraph in S6.4 (a run-record bracket, not a
proof edit). S8's original verdict block is unchanged; the F8 SCOPE BRACKET is
appended after it.

**PC1 critical cured.** Swept the amended note myself for residual unqualified
§S2-match claims (`grep` on "verbatim", "setting pins", "exactly the class"):

* :81–82 `This is DITER_RESTATE §S2's (ITER-LAW) display verbatim, on the class
  its setting pins` — the ORIGINAL claim, retained per additive-errata style and
  immediately struck/qualified by the S0 ERRATUM bracket at :85–98 ("the second
  clause ... is STRUCK as a class claim ... CORRECTED CLAIM OF RECORD:
  RESTRICTED to E₂ > 1, the proved display coincides ... on the nose"). Qualified.
* :88, :423 — quotations INSIDE the errata brackets themselves. Qualified.
* :113, :307 (`D-REAL verbatim`) and :401 (value-set `verbatim`) — different,
  correct claims (COR-3's e₀=1 form vs Lemma D-REAL; F10's row-N value sets),
  not §S2-match claims.

No unqualified verbatim-§S2-match claim remains anywhere in the note.

**Erratum pin verified.** `DITER_RESTATE_2026-08-08.md` §S2 setting line does
carry `E₂ := e₀e₁ > 1` (file line 33: "then (e₁,h₁,ψ₁); E₂ := e₀e₁ > 1;"), and
the note's S0 Reads 0/1 take e₀ ≥ 1, e₁ ≥ 1 with no E₂ constraint — the
erratum's strict-superset diagnosis is accurate. Its "harmless extension"
clause also checks: at E₂ = 1 (e₀ = e₁ = 1), s₁ ≡ s₂ ≡ 0, ℓ₀ = 0, δ₂ = 0
forced, so c ≡ 1 — covered by the COR-3 degenerations as claimed, and no step
of L1–L7/EXP/S5 consumes E₂ > 1 (checked lemma by lemma).

**Bracket attributions accurate.** PC1 report (`ITERLAW_passPC_report.md`)
does carry finding 1 [CRITICAL] = the verbatim-match claim and finding 2
[GAP] = F8 simultaneous-translation-only, verdict NOT-CLEAN; PE1 report does
carry observation O4 (class scoping) — both exactly as the brackets cite.

## 2. Seal integrity (charge 2) — PASS

* `md5sum verification/openmath/iterlaw_check.py` =
  `bfd5ef71257a79aee827b516fccfc03d` — equals the pinned seal value AND the
  md5 of `git show ab7c31c:verification/openmath/iterlaw_check.py`;
  `git diff ab7c31c HEAD -- <file>` is empty. Byte-untouched since the seal.
* Re-run (this pass): **exit 0, ALL GREEN, 35,232 samples / 0 violations**,
  every family count equal to the sealed `iterlaw_check_results.json`:
  F1 468/0 · F2 2,604/0 · F3 2,604/0 · F4 516/0 · F5 4,108/0 · F6 2,604/0 ·
  F7 156/0 · F8 1,736/0 · F9 20,000/0 · F10 4/0 · CERT 432/0. Case-II coverage
  [36,36,36,36,72,72,72,72] on rows P/Q — MET. F10 NOT-CYCLIC 4/4 with the
  exact sealed value sets ({zbar^0*z1^1, zbar^1*z1^0, zbar^1*z1^b}, b ∈ {1,2}).
  No cypari2 warning (PARI T11 leg fired). The run regenerated
  `iterlaw_check_results.json` BYTE-IDENTICALLY (git status clean after).

## 3. Supplement hostile read + re-run (charge 3) — PASS

Read `iterlaw_cor4_mixed.py` (209 lines) in full against the sealed script:

* **All four mixed blocks tested**: M1 = W2×W1, M2 = W1×W2, M3 = W3×W1,
  M4 = W1×W3, each compared ENTRYWISE against the base table W1×W1 on every
  one of the 40 families (10 rows × 4 rings — the loop runs ALL rows, not just
  the fresh ones). Plus M5 = W4×W1 AND W1×W4 with W4 = W1 + m·E₂, m drawn
  per-family from range(2,51) minus {7} (matches the bracket's "[2,50]∖{7}";
  avoids colliding with W1/W2/W3 offsets 0/1/7). Plus CF = the S5 closed form
  evaluated at the ACTUAL unreduced mixed arguments (A[r], B[s]) on every
  mixed entry — a genuine per-entry law check, not just table equality.
* **Fresh rows as claimed**: Y = (1; 4,1,1; 2,1,1) → E₂ = 8; Z = (1; 2,1,1;
  5,2,1) → E₂ = 10, outer Bézout ℓ₁ = 3 (3·2 ≡ 1 mod 5) — both verified;
  neither shape occurs in the sealed ROWS (P–X) nor in the strata_probe
  rosters (grepped: no (4,1,1) read, no e₁ = 5 anywhere). CERT (T1_T2 nf=6,
  T5, T11+PARI) runs on Y/Z only, correctly scoped ("sealed rows were
  certified by the sealed run").
* **Transcription-with-attribution verified — no silent semantic divergence**:
  ROWS P–X literal-identical to the sealed ROWS; `closed_form()` body
  code-identical to the sealed `closed_form()`; window offsets (0,1,7)
  identical; `table(A,B)` is the two-window generalization of the sealed
  one-window `table(win)` with the same `C.cocycle(·,·)[0]` semantics; both
  scripts drive the SAME `strata_probe.Composite` / `grb_order2_check.Tower`
  harness objects, so the calculus is shared by construction. (Cosmetic only:
  `pmul` imported and unused; `G0 = None` immediately overwritten. Not
  findings.)
* **Sample arithmetic reconciled exactly**: Σ E₂² over the 10 rows =
  36+64+16+36+36+4+9+16+64+100 = 381 per ring per block; ×4 rings = 1,524
  (M1–M4 each); M5 = 2 blocks = 3,048; CF = 6 blocks = 9,144; + CERT 108
  = 18,396 total. Matches the bracket's figures to the digit.
* **Re-run (this pass)**: **exit 0, ALL GREEN, 18,396 samples / 0 violations**
  — M1 1,524/0 · M2 1,524/0 · M3 1,524/0 · M4 1,524/0 · M5 3,048/0 ·
  CF 9,144/0 · CERT 108/0, no cypari2 warning (PARI fired). Output and
  results JSON reproduced byte-identically modulo elapsed-time lines
  (results JSON exactly byte-identical; git status clean).

## 4. F2c re-run (charge 4) — PASS

`iterlaw_f2c_reimpl.py` (SEED = 20260803 confirmed in-file): **exit 0,
ALL GREEN, 89,056 samples / 0 violations**; per-family 1,584/0 across the
eleven check families (ANCHOR-VAL, COCYCLE-* legs, L7 forms A/B, single-slot,
THEOREM-ITER-LAW, etc.), W-membership 128/0; mutation controls M-DIV/M-FIB/
M-FLOOR/M-ZBAR all DETECTED (536/424/344/1,584 detections — the harness can
see bugs); duty meters (E₂ ≥ 8 row, Case-II > 0, e₀ = 1 row, e₁ = 1 row,
Case-I δ₁ = 1 > 0) all MET. Output matches the committed
`iterlaw_f2c_reimpl_output.txt` modulo timing; results JSON byte-identical.

## 5. Execution actuals (three re-runs, this pass, wallclock 2026-08-03)

| script | expected | actual | exit |
|---|---|---|---|
| iterlaw_check.py (seal ab7c31c) | 35,232 / 0, all sealed counts | 35,232 / 0; F1 468 · F2 2,604 · F3 2,604 · F4 516 · F5 4,108 · F6 2,604 · F7 156 · F8 1,736 · F9 20,000 · F10 4 · CERT 432; coverage MET; F10 4/4 exact sets | 0 |
| iterlaw_cor4_mixed.py | 18,396 / 0 | 18,396 / 0; M1–M4 1,524/0 each · M5 3,048/0 · CF 9,144/0 · CERT 108/0 | 0 |
| iterlaw_f2c_reimpl.py | 89,056 / 0 | 89,056 / 0; mutations 4/4 DETECTED; duties 5/5 MET | 0 |

All three regenerated their committed results JSONs byte-identically
(`git status` clean throughout) — determinism confirmed, zero drift.

## 6. Fresh content read (charge 5) — no findings

Independent re-derivation, not a re-read of PC1's list:

* **L1** (CARRY-1, both levels): δ ∈ {0,1} from 0 ≤ s+s′ ≤ 2e−2; substitution
  + eq-(12-int) uniqueness (gcd(e,h) = 1 makes s unique mod e). Checks.
* **L2**: direct substitution; the δ₂(e₁w₁Φ₁ + h₁) = δ₂γ₂ collection checks.
* **L3** (WINDOW): δ₂ = 0 leg via L1; δ₂ = 1 leg re-computed:
  e₀u(β″) ≥ −(e₀−1)h₀ + e₀h₀ + h₁ = h₀ + h₁ > 0, using γ₂ ≥ e₀h₀ + h₁. Checks.
* **L4/L5/EXP**: the Bézout rearrangement s − ℓ₀β = e₀(ℓ₀′s − ℓ₀u) checks;
  EPS-MULT exponent bookkeeping checks; EXP's δ₁-cancellation and integrality
  (difference of two L4 integers) check.
* **L6**: degree bound s₁d₀ ≤ (e₀−1)d₀ < e₀g₀d₀ = deg Φ₁ makes the single-slot
  development legitimate; w₂(φ_γ) = γ and the m = 0 exact-w₀ read give
  val = ε₁(β). Checks, including the e₀ = 1 and e₁ = 1 corners.
* **L7 Case I**: coverage condition right (g₀ ≥ 2 ⟹ 2e₀−2 < e₀g₀; g₀ = 1 ⟹
  condition ⟺ δ₁ = 0); the unreduced-slot-grid point (digit at S₂ = s₂″+δ₂e₁
  read at j = δ₂) and the inner m = δ₁ read with exact w₀ = U both check.
* **L7 Case II**: the g₀ = 1 standard lift IS the two-term Φ₁ = Φ₀^{e₀}+ĉπ^{h₀}
  (k = 0,1 terms of the S0 lift formula); both cofactor degree bounds check, so
  the displayed two-digit development is exact; w₁(A₀) = β+β′, w₁(A₁) =
  β+β′−e₀h₀, and the slot-(S₂+1) line value γ″+h₁ > γ″ check. The subtle leg —
  A₁ ON the grid at e₁ = 1 — is correctly discarded: its slot weight β+β′−γ₂
  sits h₁ BELOW w₁(A₁), so the digit is strictly above the line and reads 0
  under the harness C_j definition. The A₀ inner read res(−ĉ) = −c₀ = z₁ =
  z₁^{δ₁} checks. Case partition (g₀ ≥ 2 | g₀ = 1 ∧ δ₁ = 0 | g₀ = 1 ∧ δ₁ = 1)
  is exhaustive, e₀ = 1 landing in Case I.
* **S5**: division legitimate (K₂ a field, ε₁ a unit); the D-identification
  with EXP's left side and s(β″) = s₁(γ+γ′) check; the displayed law follows.
* **Corollaries**: COR-1 = EXP integrality ✓; COR-2 both proofs check (the
  coboundary-times-carry structure, and the telescoping closed form — total
  carry symmetric via L1 twice) ✓; COR-3 both degenerations check ✓; COR-4's
  φ_{γ+E₂} = π·φ_γ and residue-only dependence check, and the honest
  non-descent caveat (ε₁(β+e₀) = ε₁(β)z₁^{−ℓ₀}) is correct ✓; COR-5 W-MULT is
  genuinely RECOVERED (L7 is direct development bookkeeping; no Thm 4.2/4.8 or
  GRB W-MULT consumed anywhere in S4) ✓; S6.6 consistent with the F10 actuals.
* **Statement relationship to §S2 as corrected**: with the S0 erratum, the
  claim of record is coincidence-on-the-nose RESTRICTED to E₂ > 1 + harmless
  E₂ = 1 extension — this is now an accurate description of what S5 proves
  relative to the §S2 display and its pinned setting.
* **Residuals honesty**: S7's scope box is accurate — Case II is the only
  lift-form-consuming step, so (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1
  is the right open-lemma boundary; gr(w₂) wrapper correctly labeled
  conditional-on-GRB-retarget and not consumed; orders ≥ 3 fenced; S9 upgrades
  correctly deferred to the r-fold.

## 7. Notes (non-findings)

* **N1 (out-of-fence, already on the errata ledger)**: the r35-applied status
  bracket inside DITER_RESTATE §S2 still repeats "exactly the class this
  section's setting pins"; its one-line correction is OWED at the next ROOT
  fold. Fenced from this unit; NOT a note finding.
* **N2 (cosmetic)**: `iterlaw_cor4_mixed.py` imports `pmul` unused.

## Appendix — provenance: the four errata brackets verbatim (full slices, tails eyeballed)

### A.1 S0 ERRATUM bracket (note lines 85–98)

```
**[ERRATUM (errata round 1, 2026-08-03; pass PC finding 1 [CRITICAL], report
`ITERLAW_passPC_report.md`, verdict NOT-CLEAN; independently noted sound-direction
by pass PE observation O4): the second clause of the sentence above — "on the
class its setting pins" — is STRUCK as a class claim. This note's harness tower
class takes e₀ ≥ 1, e₁ ≥ 1 (S0 Reads 0/1) with NO E₂ > 1 constraint, i.e. a
STRICT SUPERSET of DITER_RESTATE §S2's pinned setting, which carries
E₂ := e₀e₁ > 1 (DITER_RESTATE_2026-08-08.md:33). CORRECTED CLAIM OF RECORD:
RESTRICTED to E₂ > 1, the proved display coincides with §S2's (ITER-LAW) display
on the nose; the extra E₂ = 1 leg (e₀ = e₁ = 1, both carries identically trivial)
is a harmless extension covered by the COR-3 degenerations and is NOT part of the
statement of record. The instance-base parenthetical stands: every one of the
0/804 + 0/840 instances has E₂ > 1, hence lies in the restricted (pinned) class.
No proof step changes — L1–L7/EXP/S5 never consume E₂ > 1; only the statement-
match sentence was wrong.]**
```

### A.2 S6.4 SUPPLEMENT bracket (note lines 320–335)

```
**[SUPPLEMENT BRACKET (errata round 1, 2026-08-03; pass PC finding 2 [GAP],
report `ITERLAW_passPC_report.md`): the sealed falsifier's F8 compares only
SIMULTANEOUSLY-translated tables (W2×W2 and W3×W3 against W1×W1), so this
corollary's change-either-representative-SEPARATELY content was under-tested by
the seal. Supplement `verification/openmath/iterlaw_cor4_mixed.py` (NEW file;
the sealed runner stays byte-untouched, md5 == seal ab7c31c) compares ALL FOUR
mixed blocks W2×W1, W1×W2, W3×W1, W1×W3 entrywise against the base table on
every family, PLUS a fresh random-offset window W4 = W1 + m·E₂ (m per-family in
[2,50]∖{7}) mixed both ways, PLUS two fresh rows of its own — Y (1;4,1,1;2,1,1),
E₂ = 8, and Z (1;2,1,1;5,2,1), E₂ = 10 — over all four rings (40 families).
RESULT: **ALL GREEN, exit 0, 18,396 samples / 0 violations**, seed 20260808
(M1–M4 mixed blocks 1,524/0 each · M5 fresh-window mixed 3,048/0 · CF
closed-form-at-actual-mixed-arguments 9,144/0 · CERT on the fresh rows 108/0,
PARI T11 leg fired). Of record: `iterlaw_cor4_mixed_output.txt`,
`iterlaw_cor4_mixed_results.json`. As predicted: COR-4 is proved above, and the
supplement found nothing.]**
```

### A.3 S8 F8 SCOPE bracket (note lines 406–412)

```
**[F8 SCOPE BRACKET (errata round 1, 2026-08-03; pass PC finding 2 [GAP]): the
F8 family above tests COR-4 only under SIMULTANEOUS translation of both
representatives (W2×W2, W3×W3 vs W1×W1) — the four mixed blocks (W2×W1, W1×W2,
W3×W1, W1×W3) are outside the seal's coverage. The mixed-block supplement
`iterlaw_cor4_mixed.py` closes the gap: 18,396 samples / 0 violations, seed
20260808, ALL GREEN exit 0 — details in the §S6.4 supplement bracket. The
sealed runner remains byte-untouched.]**
```

### A.4 S9 ERRATUM CROSS-REF bracket (note lines 418–425, inserted mid-bullet; surrounding fragments retained verbatim)

```
  **[ERRATUM CROSS-REF (2026-08-03): per the S0 ERRATUM bracket, the harness
  tower class is a strict SUPERSET of §S2's pinned E₂ > 1 setting; the upgrade
  display should read "THEOREM — restricted to §S2's E₂ > 1 setting it is the
  pinned display on the nose; the E₂ = 1 leg is extension, not statement of
  record". NOTE ALSO: the r35-applied status bracket inside DITER_RESTATE §S2
  repeats the "exactly the class this section's setting pins" phrasing; that
  file is fenced from this unit — its one-line correction is OWED at the next
  r-fold.]** §S3's binding
```

— ITERLAW-PE2, Fable leg, pass 2 of the post-errata hostile pair (concurrent
with Codex PC2). Acceptance requires BOTH clean; this leg: **CLEAN**.
