# FGMN pass 5 (Fable) — hostile verification of FGMN_REDERIVATION_2026-08-08.md at REVISION 3

**Charge.** Fresh-context hostile pass over the FGMN transcription-scale re-derivation
note (REVISION 3, HEAD f64307e), the battery
`verification/openmath/fgmn_rederivation_check.py`, the recorded console
`fgmn_rederivation_rerun_r1.txt`, and the provenance pins in `docs/references/`.
Priority: the REVISION 3 additions (primed-mirror disposition with the "enumerated
exactly" site census — grepped the DictIII tree myself; mode-conditional supplier
sentence; the actually-performed §S8 relabel; the corrected slot-order render), then
the standing perimeter (diagnosis, row-A, branch+meter, rescopes, JuncForge/D0
honesty, the three-token diff appliable without applying).  No `*_pass*_report.md`
was read.  Quote-and-classify; nothing fixed.

## 1. Independent execution record (the mandatory leg)

* **Battery re-executed by this verifier**: `python3 fgmn_rederivation_check.py`,
  exit 0, **console byte-identical to `fgmn_rederivation_rerun_r1.txt`** (diff
  empty, including the `elapsed 0.6s` timing), TOTAL checks 1093, all six rows
  GREEN at the recorded counts (R0 28, R1 336, R2 336, R3 1, R4 336, R5 56; 336
  deep sites), MISREAD meter {A:24, B:48, C:24, K:28, L:24, M:48, N:48}, R2
  SUPPORT meter {2:264, 3:68, 5:4}.  `fgmn_rederivation_results.json` regenerated
  **byte-identical** (no git diff after my run).
* **Both sha256 pins verified by this verifier**: PDF
  `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35`, layout
  extraction `8d30f15e6d37a52be20634545c95f32e372a233166c5dab8d995c3d5f76e848b` —
  both match §S0's table.
* **Layout extraction independently REGENERATED** from the pinned PDF with
  `pdftotext -layout` (poppler 22.02.0 on this box, same version as pinned):
  sha256 byte-identical to the pin.
* **Shared corrupted extraction confirmed**: `/tmp/litunit/fgmn.txt` still present,
  sha256 `695412d2155a766ebb92e96c05d2b374533e7518a676a1b9e599c5774fae1516`
  (matches §S0's `695412d2…fae1516`); its Def 3.15 block (l.1237–1241) orphans the
  prime (U+2032) on its own line with no column alignment and shows the exponent as
  `ℓi s(α)−ℓi u(α)` with no prime on either ℓ — the corruption is exactly as §S7
  describes.
* **Def 3.15 prime-column arithmetic recomputed**: in the pinned layout file, l.911
  carries the ′ at codepoint column 52; l.912's FIRST ℓ sits at column 51 (subscript
  i at 52), the second ℓ at column 59.  The ′ sits directly above the first ℓᵢ —
  §S7's column-verified reading ǫᵢ(α) = zᵢ^{ℓ′ᵢs(α) − ℓᵢu(α)} is exactly what the
  print shows.  Bezout tie l.883–884 (`ℓᵢhᵢ + ℓ′ᵢeᵢ = 1`, s ↔ ℓ, u ↔ ℓ′) matches the
  script's mode-C exponent `l0p*s − l0*u`.
* **Every §S1 display citation pulled and checked** against the pinned extraction:
  l.869–871 (Nᵢ := N_{µᵢ₋₁,φᵢ}), l.384, l.937–939 (Qₛ at µᵢ₋₁), l.940–944 (eq 13),
  l.923/l.934 (sⱼ, αⱼ ∈ Γᵢ₋₁), l.415 (Lemma 2.3 proof), l.916–923 (Def 3.16),
  l.910–915 (Def 3.15 + ǫ₀ ≡ 1 convention), l.881 (eq 12), l.1085–1087 (Cor 4.4(2)),
  l.1028–1029 (Thm 4.2 display, verbatim), l.1017–1019 (Lemma 4.1), l.994–1000
  (Def 3.18, j₀ = ⌊s(g)/eᵢ⌋), l.1004 (eq 14), l.1263–1265 (Cor 5.6(2)).  All
  accurate.  Genericity ranges verified: `0 ≤ i < r` (l.910), `0 ≤ i ≤ r` (l.916),
  `1 ≤ i ≤ r` (l.994–995).
* **Row-A arithmetic by hand**: fA = (X+2)² + 24, d1 = [24, 0, 1], wPrev(24) = v₂(24)
  = 3; corrected functional at slots {0,2}: {2·3+0, 2·0+2·3} = {6,6} = gam ✓;
  compiled (w = e·wPrev): slot 0 → 2·6+0 = 12, slot 2 → 2·0+6 = 6, i.e. [12,6]
  slotwise ✓; record (2,3,6,0,2,(1,1),1,1) matches the battery's R3 output ✓.

## 2. REVISION 3 priority items — verdicts

* **§S8 relabel ACTUALLY performed** (item 2): the bracket "[REV3: the block below is
  an EDITED RENDER of the raw file … the raw file is the record]" now sits in the §S8
  body (note line 290), not merely described in a revision block.  VERIFIED.
* **Slot-order render** (item 3): §S8 now shows "old functional at slots [0,2] =
  [12,6]" with an in-line REV3 bracket; the slot correspondence (0 → 12, 2 → 6) is
  arithmetically correct and matches §S2's {2·6+0, 0+2·3} = {12,6}.  VERIFIED (but
  see GAP 2 on the residual header tension with the raw file's sorted-set order).
* **Mode-conditional supplier sentence** (item 1, second half): `DIterJunctionSupplier`
  verified at `Scaffold/HDischarge/H1/GlueRun.lean:875` — antecedent
  `σ₁.Φ.natDegree < n` present, binds `SideReads` BY NAME; so "inherits … textually
  unchanged" is true only of the in-place variant and must be restated under the
  new-definition route, exactly as the mode-conditional bracket says.  VERIFIED
  (recorded in the revision block only, per the note's append-only supersession
  convention — same convention as the REVISION 2 token-count supersession).
* **Primed-mirror disposition / "sites enumerated exactly"** (item 1, first half):
  **REFUTED by my own grep of the DictIII tree** — CRITICAL 1 below.

## 3. Findings

### CRITICAL 1 — the REVISION 3 mirror census is not exact: `SideClauseR2`/`sideReads_r2` (the verbatim clause-(ii) mirror, containing a re-keyed token site) and the entire (†)-transfer layer are missing

Quote (REVISION 3, item 1): "The σ.w restatement sites enumerated exactly:
Window.lean:177, :258, :260, :266, :544 (the hwS binder) and Locality.lean:98
(comment), :121-:129 (`σ.w`-hypothesis cluster) — each gets a primed twin or a
mode-conditional bracket in the application change-set"; and "the application
change-set introduces primed mirrors — `SideClauseR1'` (the verbatim clause-(i) copy
of `SideReads'`) with `sideReads_r1'` as its definitional tie".

My grep of `lean/LeanUrat/Scaffold/DictIII/` (all σ.w occurrences, wPrev excluded)
shows the enumerated set is NOT complete:

* **(a) `SideClauseR2` (Locality.lean:735) — docstring: "`MovesJ.SideReads` clause
  (ii) DIGITS, VERBATIM (`HC2/Defs.lean`)" — carries the clause-(ii) window
  functional at σ.w at line :738**, i.e. the EXACT shape of the third re-keyed token
  (Defs.lean:292), **with definitional tie `sideReads_r2` (:744, `:= h.2.1`)**.
  Clause (ii) is one of the two clauses the three-token diff re-keys.  Under the
  in-place variant `sideReads_r2` breaks exactly as `sideReads_r1` does (the
  projection `h.2.1` would deliver the wPrev form against SideClauseR2's σ.w form);
  under the RECOMMENDED new-definition route the specified change-set (R1 pair only)
  omits `SideClauseR2'`/`sideReads_r2'`, leaving the DictIII Theorem-1 transfer of
  the corrected clause (ii) silently missing — the exact "silently diverge" failure
  mode REVISION 2 introduced the mirror layer to prevent.  It sits 460 lines below
  the enumerated `SideClauseR1` in the SAME FILE, with a docstring announcing the
  verbatim copy.
* **(b) the (†)/`hdag` functional restatements** `ν.gam < (ν.e : ℤ) * ν.σ.w (B j −
  B' j) + (j : ℤ) * (ν.h : ℤ)` at Locality.lean **:322, :381, :398**
  (`sideClauseR1_transfer`/`_iff`/`sideReads_r1_transfer`), **:794, :828, :847**
  (the R2 transfer family), **:1327** (the III-T10 `read_locality` hdag discharge),
  plus **`dagger_sheared`'s conclusion :658** and the III-T10 `rows` σ.w-hypothesis
  bundle (:1258–:1269) — all restate the compiled-scale functional and are
  unenumerated.  These are not token-level twins: the corrected-scale transfer row
  is gam < e·wPrev(D) + j·h = w(D) + j·h (stretch law on the carrier), which is
  STRICTLY STRONGER than the compiled row gam < e·w(D) + j·h that `dagger`'s middle
  leg (gam/e < readCeil·E) supplies — at e ≥ 2, j = 0 the supplied w(D) > gam/e does
  not give w(D) > gam.  A primed transfer layer therefore needs re-derived
  readCeil arithmetic, which the disposition (twin-or-bracket) does not engage.
* **(c) Window.lean :554/:557** — `m6c_noPhantom`'s CONCLUSION clauses
  `(ν'.e : ℤ) * ν'.σ.w (B ν'.s0) + (ν'.s0 : ℤ) * (ν'.h : ℤ) = ν'.gam` (and at
  s0+wSide): endpoint restatements of the re-keyed functional, derived from clause
  (ii) in the proof (`hside.2.1 … .2.1`) — same declaration as the enumerated :544
  hwS binder but distinct, unenumerated functional sites that inherit the old shape.
* **(d) `SideClauseR5`/`sideReads_r5` (Locality.lean:915/:922) and the III-T10
  assembly `read_locality`** (consumes `sideReads_r1`/`r2`/`r5` at :1365–:1375 and
  REBUILDS a full `SideReads` bundle for f′): no σ.w token in R5 itself, but any
  SideReads′-keyed Theorem-1 transfer needs the full primed tie family and a primed
  assembly; "restates the supplier/glue route against `SideReads'`" names only the
  GlueRun route, not DictIII's `read_locality`.
* (Evidence the census method was textual, not semantic: the enumerated
  Locality.lean:98/:121–:129 cluster is the `rloc` R-LOC kernel — generic in β and
  scale-agnostic, never mentioning gam/e/h or the functional; it neither breaks nor
  diverges under either route, while the actual clause-(ii) mirror in the same file
  was missed.  Marginal additional site observed: CU1.lean:373's γ-tie
  `u := ((gam − s0·h)/e).toNat` encodes the endpoint functional relation without a
  σ.w token.)

Classification: **CRITICAL**, scoped to the REVISION 3 item-1 claim.  This is a
positive, checkable exactness claim — the very deliverable of the pass-4 gap-1 fix —
and it is false against the repo; the primed-mirror change-set specified from it is
incomplete in the direction the disposition exists to guard.  Mitigations on record:
nothing is applied (no `.lean` touched — verified below), and §S3 obligation (b)'s
application-time grep census of `SideReads` consumers would surface `sideReads_r2`
(it takes `h : SideReads …`).  The note's core mathematics (§§S1–S8) does not depend
on this item.

### GAP 2 — the §S8 render header "numbers identical to the raw record" now covers an order-divergent line, and the script's own display stays correspondence-misleading

Quote (§S8, note line 290): "the block below is an EDITED RENDER of the raw file
`fgmn_rederivation_rerun_r1.txt` — numbers identical to the raw record; the raw file
is the record"; and (line 307) "old functional at slots [0,2] = [12,6] [REV3: render
order corrected …]".  The raw record prints "slots [0, 2] = [6, 12]" (the script's
`oldA = sorted({…})`, a sorted SET against a slot list).  The render's [12,6] is the
correct slot correspondence and is disclosed at the line, but (i) the header's
"numbers identical" does not prepare a reader for an ORDER divergence between render
and record (identical as multisets only), and (ii) the underlying script line
(`fgmn_rederivation_check.py:345-348`) still juxtaposes a slot list with a sorted
set — the raw record remains misleading as a correspondence and is cured only in the
render.  All numbers are correct; the UNSAT conclusion is unaffected.
Classification: **GAP** (wording/display hygiene).

## 4. Standing perimeter — re-verified independently, no findings

* **Diagnosis (§S2)**: compiled `SideReads` at HC2/Defs.lean:280 reads
  `(ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ)` at lines 285/287/292; the clause-(ii)
  residual leg already carries `ν.σ.wPrev` (:295).  `RegradeOf.w_coeff` (MovesC/
  Defs.lean:651) is the e★ = 1 pointwise-agreement face; `U31.bStage` literally sets
  `w := bw, wPrev := bw` (U31_gateReadsOf.lean:635–636) — the invisibility account is
  accurate.
* **Row-A**: hand arithmetic + battery R3 exact (record (2,3,6,0,2,(1,1),1,1);
  compiled slotwise [12,6], corrected [6]).
* **Branch + meter**: `check_compiled_unsat` implements exactly the claimed repaired
  semantics — violation iff ≤ 1 distinct compiled value at supported slots (ANY
  singleton counts; empty counts); the support meter tallies per-site distinct
  counts, observed {2:264, 3:68, 5:4} (sums to 336, minimum 2 — no single gam′
  anywhere); the sealed derivation e·gam − j·h·(e−1) is correct algebra given R1's
  verified equality ties, with e = e1 ≥ 2 and h = gamma2 > 0 on every roster row.
* **Rescopes**: R1's `check_corrected` checks exactly (i-a)/(i-b)/(ii-support)/
  (iii-window-length) and never instantiates σ.R — the "scale-sensitive
  window/support satisfiability check, NOT full corrected-bundle satisfiability"
  rescope is accurate to code.  R4's from-print operator consumes certified Tower
  state (`T.w1` directly in `R2_print`'s polygon, `T.res_digit`, `T.K1`, `T.z1`,
  keys and chain parameters) — the "differential falsifier, independent only in
  recursion/exponent code" rescope is accurate.  Misread meter nonzero on EVERY
  tower row (24–48), matching §S7's stronger measured claim.
* **JuncForge/D0 honesty**: `juncforge_no_e2_junction` (JuncForge.lean:276, concludes
  ν.e = 1 for any SideReads recording of the row-A read), `juncforge_clauseIII_derivable`
  (:578, wPrev(24)=3 / w(24)=6 pins), `juncforge_D0_instanceFalse` (:686, B₀ = 0 vs
  clause-(ii) B₀ ≠ 0), `gate_glue_conditional` (GlueRun.lean:1161),
  `DIterJunctionSupplier` (GlueRun.lean:875) all present with the shapes the note
  asserts; all bind the compiled `SideReads`; the D0 stratum is not resurrected
  (battery R5 + print eq (14) verified).  ITER-LAW's two-constant + fibration form
  and the cyclic-form fence are as displayed in GlueRun's supplier docstring.  Row A
  has e₀ = 1 (roster r0 = (1,1,1)) — §S6.2's degeneration claim checks.
* **Three-token diff**: both §S3 OLD fragments are verbatim-unique in HC2/Defs.lean
  (checked mechanically); OLD→NEW token diff is exactly `ν.σ.w` → `ν.σ.wPrev` ×3
  (plus comment labels) at the sites of Defs.lean 285/287/292 — appliable without
  applying; the REVISION 2 three-token supersession of the stale "four-token"
  title/§S3 occurrences stands on the note's append-only convention.
* **No `.lean` touched**: all four FGMN commits (303b11e, 236d85c, 0170d68, f64307e)
  touch only notes + verification artifacts (git show --stat verified).
* **Preregistration integrity**: the REVISION 1 ADDENDUM (repair semantics + derived
  sealed prediction) sits in the script header; seed 20260816 matches the sealed
  stage-1 harness (`juncforge_stage1.py:13,398`), which is imported, not edited.

## 5. Tally

CRITICAL 1 (REVISION 3 mirror census falsely claimed exact; R2 mirror pair + transfer
layer + Window endpoint sites missing from the primed-mirror disposition).
GAP 2 (§S8 render-header/order tension; script display).  The independent-execution
leg, both pins, the extraction regeneration, the print citations, the diagnosis, the
row-A record, the repaired branch semantics, the rescopes, the JuncForge/D0 honesty
perimeter, and the three-token diff all verified clean.  Acceptance counter: resets —
a CRITICAL pass does not advance 0/2.

FGMN-P5 FINDINGS: 1 critical, 1 gaps
VERDICT: CRITICAL
