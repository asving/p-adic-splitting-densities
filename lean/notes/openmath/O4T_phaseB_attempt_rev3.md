# O4T — the O-4 drainage transfer — Phase-B attempt record, REV 3 (Fable, 2026-08-02)

Light-repair round after the pass-2 hostile audit. This record is a DELTA on
`O4T_phaseB_attempt_rev2.md` (which stays the full unit record — what was achieved,
the falsifier record, the design decisions); only the pass-2 dispositions and the
file map change here.

## 1. What happened

Pass 2 of the two-pass bar (`O4T_pass2_fable_verify.md`; Fable, fresh context,
standalone read of `O4T_phaseB_verifybrief_rev2.md`) returned **UNSOUND — one
CRITICAL + four JUSTIFICATION GAPS — with the ENTIRE mathematical core UPHELD
line-by-line** ("Theorem N3 with both (CEIL) chains and all probed corners,
TR-0/FLOOR/TR-Q with the rev-2 unboundedness repair, Lemmas CERT/RES/RES-0/SIDE/REC,
the `e·d ≥ 4` exclusion at every branch including wild p — survives line-by-line
audit"). All five V30-repair executions were confirmed genuine. The ledger's
CORRECTION entry (2026-08-02) set the unit's status to r3: light repairs.

## 2. Pass-2 findings → rev-3 dispositions (full table = rev-3 brief §0-pre-3)

1. **CRITICAL — N3-BRACKET's terminal `=` false for `N ≥ 2`** (count normalization:
   the middle set is level-`N`, `undec^K(2N−1)` is level-`(2N−1)`; off by exactly
   `p^{n(N−1)}`; verifier's instance n=2, p=2, N=2: **8 vs 32**). REPAIRED: `=` → `≤`
   with the exact normalization identity AND the 8-vs-32 refutation displayed; the
   density form (where the terminal `=` IS true) displayed as the identity-bearing
   statement. The error was localized — §4 consumes only the inequality/density form.
2. **GAP — import inventory incomplete + six-vs-eight unreconciled.** REPAIRED: Facts
   **SEP** (char-0 separability of irreducibles) and **DES** (Galois descent/fixed
   field) added as named in-line-proved imports with consumption-site cite tags (Fact
   SF's `Z_p`-coefficients step; CERT(ii)'s rationality step; the Finding-3 chain);
   count RECONCILED — V30's eight items map onto rev 2's six Facts (EF and GRD each
   bundle two); SEP/DES are NEW, so the named inventory beyond NP/SF/HEN is now eight.
3. **GAP — every-lift separability consumed (soundness/FLOOR) but never proved.**
   REPAIRED: the verifier's own chain displayed as a closing paragraph of Theorem N3's
   proof — certified factors are pairwise-distinct irreducible monic factors of any
   completion `g` with disjoint root groups and degrees summing to `n`, each separable
   (Fact SEP), so `g` is their product with `n` distinct roots.
4. **GAP (minor) — CERT(i)'s hull ambiguous at `x₀ = 1`.** REPAIRED: pinned to the
   verifier's closing reading (b) — the hull OF the index-range `[x₀, n]` point set;
   index 0 enters only through (C2)/CERT(ii). Statement + proof wording fixed.
5. **GAP (minor) — the §4 rescope refutation mixed count/density normalization.**
   REPAIRED: restated in density form (FLOOR at a common level + the §5 `n = 2`
   `env^can = env^sem` exactness); the rescope conclusion — verified correct by pass
   2 — is unchanged.

Everything pass 2 UPHELD is byte-stable (verified by diff: 18 hunks, all at the six
repair sites + header/changelog/ledger/charges). New §7 charge 11 hands the next pass
the three substantive rev-3 additions as explicit attack targets.

## 3. Honest status

**PROVED-UNVERIFIED at rev 3** (rev 1 UNSOUND at V30 — TR-Q critical; rev 2 UNSOUND
at pass 2 — N3-BRACKET terminal `=`; core upheld at both). TR-OM remains
CONDITIONAL-OPEN on (AGR) exactly as in rev 2. NUM (P1–P6, 2,534,851 classes, ALL
PASS) untouched — no harness or numeric change in this round; no Lean edits.
Verification protocol: hand `O4T_phaseB_verifybrief_rev3.md` ALONE to a fresh hostile
pass; priority charges = §7 items 11 (the rev-3 repairs), 8 (the enlarged inventory +
the reconciliation map), 10 (the normalized rescope reasoning).

## 4. Files (delta)

* `lean/notes/openmath/O4T_phaseB_verifybrief_rev3.md` — the repaired self-contained
  brief (REV 3 — hand THIS to verification; §0-pre-3 = the pass-2 disposition table).
* `lean/notes/openmath/O4T_phaseB_attempt_rev3.md` — this record.
* `lean/notes/openmath/O4T_pass2_fable_verify.md` — the pass-2 audit rev 3 repairs.
* Superseded (kept byte-stable as history): `O4T_phaseB_verifybrief_rev2.md`,
  `O4T_phaseB_attempt_rev2.md` (still the full unit record), rev-1 pair, `V30_o4t.jsonl`.
* Unchanged: `verification/openmath/O4T_transfer_check.py` + sealed results/logs.
