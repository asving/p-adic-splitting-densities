# GRTJA pass PE4 — fourth hostile pass (acceptance attempt, counter 1/2) on GRTJA_PROOF_2026-08-08.md (post-r2, post-PE3-clean)

**Verifier:** JA-PE4 (fresh hostile Fable context; fixes nothing). Round 4
of the acceptance arc; a clean pass here would be the second consecutive
(acceptance); any finding resets (counter action = orchestrator's).

**Target pin:** note at HEAD 7c297d2, md5 `b81258df` == `git show 5d95805:`
(the JA-r2 repair commit — unchanged since r2, as dispatched). Artifact
seals verified by md5 at worktree AND pins: runner `grt_ja_checks.py`
`5972d412` == @696eae8 (SEAL); output `0d6d0522` and JSON `13ab52ab` ==
@1cbf8ca (VERDICT). `git log 5d95805..HEAD` over the note + all three
artifacts = EMPTY. Supplier-motion census since 5d95805 (new leg, run for
requirement 2): [ILN]† ITERLAWN_PROOF, `grt_weld_probe.py`,
`iterlawn_pe_reimpl.py`, the weld blueprint, and the completion tree are
ALL motion-free; the ONE moved supplier is `GRTW2_PROOF_2026-08-08.md` —
W2 r1 (8d5e3fa, 2026-08-06 19:45, NINE MINUTES after JA r2's 19:36) and
W2 r2 (ffa1e57). That drift is FINDING 1 below.

**Charge executed:** (1) TWO components re-derived by routes different
from all of PE1/PE2/PE3 — (a) the per-slot character-gauge law via the
ν-shift + W2-L2-covariance route (§2; prior passes all used direct
subtraction of the two exponent fractions), with an exact
grid-interpolation symbolic leg; (b) JA-VDIND's triviality theory via the
conjugation-form / character-kernel route (§3), with a NEW machine probe
keying four displayed statements the sealed battery has no family for.
(2) Statement-level truth of the whole note at HEAD (§4): quotes at pins,
16 tex anchors re-read at source, §7 tables recounted from the committed
JSON, §5 consumption rows vs their sources at HEAD, supplier-motion
census. (3) Arc accounting at HEAD (§5). Machine leg re-run in a /tmp
sandbox (committed artifacts untouched).

---

## 1. Machine leg — RE-RUN, BIT-IDENTICAL MOD TIMING

Re-ran `grt_ja_checks.py` (full battery, /tmp copy with the engine_ext
pin set): **exit 0, all 17 families GREEN, TOTAL samples 10,311, 0
violations, CK-RES boundary 16, CK-BPREF 26**; stdout identical to the
committed `grt_ja_checks_output.txt` after stripping wall-clock fields;
regenerated JSON deep-compared key-for-key: identical except `elapsed_s`
(5.5 vs 7.4). Recounts from the COMMITTED JSON (own arithmetic): family
samples column == §7.1 cell-for-cell (1/111/1,132/872/1,744/3,248/340/
443/443/26/444/1,452/5/4/3/2/2); roster scored sums to 396 main + 14 QO +
33 d₀ = 443; boundary 16 = T3B (4 main + 3 transported) + I4B (5 main +
4 transported), every other instance 0 — the transported split read from
the per-tag `tw` records; bpref 26 = 22 roster hits on exactly 10 rows
(T2A/T2C/T2D/T2G 1 each, T3A/T3C/T3D 2 each, T3E 4, T3F 1, I4C 7) + 4 d₀
(one each); designated rows T2A/T3A/T3E fire 1/2/4; teeth 8/9/8, 11/11,
12/18 from the `mut` block; QO 5/5 `complete` with `pari_full` recorded
((4,1)×3, (2,2), (3,1)); TW-INST ledgers exactly 20. Every §7.1 figure
confirmed.

## 2. Requirement 1a: the per-slot gauge law — RE-DERIVED BY A NEW ROUTE

PE1/PE2 derived the exponent by direct subtraction of the two displayed
fractions (t(i) − τ_{m−1}(a_i) computed in one line from u_i = β_i +
i·W_{m−1}); PE3 re-derived only the induction. NEW ROUTE (ν-shift
cancellation + the sealed W2-L2 covariance, no direct subtraction):

* Write t̂(V) := (ℓ_{m−2}V − s_{m−1}(a_i))/e_{m−2} (the t-functional read
  at the digit's own initial ATTAINED abscissa). Then by definition
  t(i) = −t̂(u_i) and τ_{m−1}(a_i) = −t̂(β_i).
* ν-shift cancellation: s(u_i) = s(β_i) (because ℓ(u_i − β_i) = ℓ·i·W_{m−1}
  and e_{m−2} | W_{m−1}), so t̂(V) = t_{m−1}(V) − ν_i with the SAME
  ν_i = (s_{m−1}(a_i) − s(β_i))/e_{m−2} ∈ ℤ_{≥0} for both V ∈ {u_i, β_i}
  (attained abscissas lie on the integer-ordinate grid, JA-GRID(b)).
  Hence t(i) − τ_{m−1}(a_i) = −[t_{m−1}(u_i) − t_{m−1}(β_i)].
* W2-L2 covariance (§3.2's "More generally" display, consumed proved;
  k = i at level m−1, hypothesis u_i − β_i = i·W_{m−1} ∈ W_{m−1}ℤ met):
  ε_{m−1}(β_i)·z^{t_{m−1}(u_i)} = z^{i·A_{m−1}}; with JA-EPS
  ε_{m−1}(β_i) = z^{−t_{m−1}(β_i)} this reads
  z^{t_{m−1}(u_i) − t_{m−1}(β_i)} = z^{i·A_{m−1}} AS A FIELD IDENTITY.
* With the proviso (VD-(m−1)) at a_i: c_i = z^{t(i)−τ_{m−1}(a_i)}·C_i =
  z^{−i·A_{m−1}}·C_i. ∎ — the law lands as a field identity directly from
  two already-sealed inputs (JA-EPS + W2-L2) plus the ν-shift, without
  ever producing the integer identity; the note's route additionally
  yields the integer form. EXACTLY the displayed law; m = 2
  unconditionality = (VD-1) = W2-L3 as displayed.
* Symbolic leg (route unused by ALL prior passes — they hand-computed or
  sampled): the five underlying integer identities (route-1 direct;
  route-2's three decomposition steps; the §1 display e·A_m = ℓ·W_m)
  verified as EXACT polynomial identities by grid interpolation over ℚ
  (degree ≤ 1 per variable after clearing e; {0,1,2}-grids exceed every
  degree bound, so the check is a proof, not a sample): 6/6 PASS.

## 3. Requirement 1b: JA-VDIND's triviality theory — NEW ROUTE + NEW MACHINE FAMILIES

Route: derive the FULL conjugation form first, then read the whole
triviality theory off it as character-kernel statements (PE1 touched the
form once at exponent level; PE2/PE3 did not re-derive it; no prior pass
machine-keyed it).

* Grid re-indexing (i_j = s₀ + j·e_{m−1}, j ≥ 0, s₀ the initial attained
  abscissa; ν = (s₀ − s(β))/e_{m−1}): summing the per-slot law,
  R_m(A)(y) = Σ_j z^{−i_j A}C_{i_j}y^j = z^{−s₀A}·Σ_j C_{i_j}(z^{−eA})^j y^j
  = z^{−s₀A}·Q_A(ϑ_m y) with Q_A(y) := Σ_j C_{i_j}y^j and
  ϑ_m = z^{−e_{m−1}A_{m−1}} — and Q_A(y)·y^ν = the packed polynomial,
  since R_m v(A) = Σ_j C_{i_j}z_m^{ν+j}. The display is EXACT.
* Evaluated consequence: LHS(VD-m) = z^{−s₀A}·z_m^τ·Q_A(ϑ z_m) and
  RHS(VD-m) = z_m^τ·Q_A(z_m) (using τ_m(A) − ν = −t_m(β) = the ε-exponent,
  JA-EPS) — the displayed "differ by z^{−s₀A}·(ϑ-twisted packed sum vs
  the packed sum)", now as two separately checkable identities.
* Triviality theory as kernel statements: the hypothesis "z^{i·A} = 1 at
  every attained i" ⟺ z^{s₀A} = 1 AND ϑ^j = 1 at every attained offset j
  (j = 0 always attained). Forward direction: both kernel conditions kill
  the twist coefficientwise, LHS = RHS. Sufficiency list: A_{m−1} = 0 ⟺
  e_{m−2} = 1 (normalized Bézout: e ≥ 2 forces ℓ ≥ 1, g, γ ≥ 1; e = 1
  forces ℓ = 0) — machine-scanned below; ord(z) | A is sufficient alone
  (kills every i). NOT-sufficient claim: single-slot support leaves ONLY
  the j = 0 kernel condition unmet when z^{s₀A} ≠ 1, and then LHS =
  z^{−s₀A}·RHS with RHS ≠ 0 (attained ⟹ C_{s₀} ≠ 0, ε a unit) — the
  constant survives, (VD-m) FALSE. Converse-unsealed clause: off both
  kernel conditions the ratio is z^{−s₀A}·Q_A(ϑz_m)/Q_A(z_m), which CAN
  cancel — the note honestly does not seal it.
* **NEW machine probe** (`ja_pe4_probe.py`, /tmp over the sealed engines
  and pools, own vd-evaluation, own Bézout via `pow(h, −1, e)`, own
  weight chain; disclosed uncommitted, same discipline as PE2/PE3):
  main-roster scored 396 (boundary 9 = T3B 4 + I4B 5, matching the
  committed main-leg census). Families, all keying displays with NO
  sealed-battery family:
  - **P-A** FULL conjugation form, coefficientwise via the s₀A + jeA
    decomposition (not the i·A route CK-RES uses): **396/396**.
  - **P-B** BOTH evaluated identities of the difference display, on every
    scored sample INCLUDING all 66 character-visible ones: **396/396 each**.
  - **P-C** JA-MIN's support claim (print support == harness support ==
    attained set, slot-for-slot zero/nonzero, degrees agree): **396/396**
    — first machine key for JA-MIN's c_i = 0 ⟺ C_i = 0 sentence.
  - **P-D** single-slot NOT-sufficient: 44 scored samples with |att| = 1
    and z^{s₀A} ≠ 1 — **(VD-m) FALSE on all 44, and LHS == z^{−s₀A}·RHS
    EXACTLY on all 44** (the surviving-constant claim, quantitatively).
  - **P-E** census, third independent reproduction (after PE2's and
    PE3's, via my own evaluator): (VD-m)-false = **66 = 58 at m = 2 + 8
    at m = 3**, all 66 root-character-visible (0 root-invisible failures);
    root-trivial scored = **330, (VD-m) TRUE on every one**; 330 + 66 =
    396. The §3.4 [r2] bracket's figures confirmed again.
  - **P-F** A_m = 0 ⟺ e_{m−1} = 1 at every level of every tower: 44/44.
  - **P-G** the packing display R_m v(A) = Σ_j C_{i_j}z_m^j: 396/396.
  Probe exit 0, 0 failures across all families.

## 4. Requirement 2: statement-level truth at HEAD — ONE FINDING

Drift-free legs, verified this pass: both §3.3 JB quotes byte-true at the
4c4ee56 pin (ordered byte-contiguous segments of §0M col (b) incl. the
struck "~~exactly~~" elision; the quoted span closes before the [r6]/[r7]
brackets — faithful); §3.4's col-(c) operative-fence paraphrase supported
at pin; 16 tex anchors re-read at source (220/449/828/829/882/912/1028/
1149/1167/1176/1259/1285/1291/1431/1447/1497 — incl. Def-t(i)'s literal
(s_{r−1}(a) − ℓ_{r−1}v_r(aφ_r^i))/e_{r−1} at 1432, which under P-index is
byte-exactly §3.4's display, and tex 1291's "arbitrary coprime ... we fix
ℓ_r, ℓ′_r" pinning no representative — JA-BOX-3's premise); §7.1/§7.2
recounted (§1); §5's GD-5/tree and blueprint quotes against motion-free
sources; [ILN]†/probe/engines motion-free since r2.

**FINDING 1 — JUSTIFICATION GAP (§2 clause 8; §4(i) chain-level bullet +
transported-chamber bullet; §7.2 rows "JA-PIN cl. 8" and "§4 transport"):
the W-2 consumption is unpinned and its carried conditionality is
contradicted/incomplete at HEAD after the supplier moved.** JA r2 froze
at 2026-08-06 19:36; W2 r1 (8d5e3fa) landed 19:45 and W2 r2 (ffa1e57)
after. At HEAD the W-2 note's claims table STRIKES the exact text JA
carries — "~~PROVED at attempt grade given §3–§4; machine 44/44/44~~" —
regrading W2-C3 to "PROVED ... up to and including each chamber's first
ξ ≠ 1 junction (38/44 junction-levels); MEASURED above it (6/44 ...)
riding W2-OPEN-2", with TW-STRICT reclassified SAME-adjacent ("NOT two
independent 44/44 legs"). Against this, at HEAD the JA note still
displays: "of the TRANSPORTED type t^tw strictly at every level (W2-C3,
attempt grade, machine 44/44/44)" with the carried list "the
(C-coll)/recursion split, the §4.3 ℓ-orbit convention fence, and
W2-OPEN-1 (value layer) OPEN" (§2 cl. 8); "key polygons and weights agree
(W2-C3(i), machine 44/44 in the W-2 runner)" (§4(i)); "the transported
ledger is itself a class-pin instance (W2-C3's induction)" (§4 last
bullet); "conditionality verbatim" (§7.2). The supplier's own consumer
contract (W-2 §6.3, [r1, F1] + [r2, P1]) now REQUIRES every consumer to
carry item **(d)**: W2-OPEN-2's open status for clause 3's chain level
above each chamber's first ξ ≠ 1 junction, the proved-to-first-twist/
measured-above grade split, the W2-C1a chamber qualifier, and (OPEN-2a).
JA carries (a)/(b)/(c) but not (d) — the list predates it. No fold
annotation covers JA: W2 r1/PE2 recorded WM (M4) + JB row-15 as the
consumer surfaces (pin-protected); the ledger's fold-owed list has no
JA/W-2 item; JA's W-2 cite has no as-of pin (unlike the JB cite, pinned
at r2 precisely against this genre). NOT critical: no JA derivation
consumes the retracted strength (clause 8 is consumption billing; §4's
transport bullet is billed "chamber = W2-C3 consumption"; TW-INST is JA's
own instance evidence, 20/20 ledgers, unaffected; the W2-C1 leg of clause
8 did not move — only C1a's qualifier and C3's grade did). CURE (one
dated bracket): update the clause-8 carried-conditionality list to W-2
§6.3's current (a)–(d) (adding W2-OPEN-2/OPEN-2a and the grade split),
correct the two "44/44(/44)" grade glosses to the supplier's current
display, and pin the W-2 cite as-of a commit. Escaped PE3, which ran
post-W2-r1 but did not sweep the W-2 consumption against the moved
supplier.

Checked and NOT graded (adjacent candidates that fail the bar):
* §5's W-2 bullet "consumed AT ATTEMPT GRADE (0/2 hostile passes) with
  its full conditionality ledger" — "0/2" still true (ledger counters:
  W2 0/2); "its full conditionality ledger" is pointer-form
  (self-updating), unlike clause 8's closed enumeration.
* §5's N-1 cite "GRB_ORDER2 ... REV 11/14": GRB has since gained REV 13 /
  pass-16 brackets, but those narrow TR-3 rows to exactly the scope JA
  already bills ("family-ledger scope", "ACCEPTED order-2 instance") — no
  contradiction at source found; dated-cite genre only (observation n1).
* W2 r2's sign-fix reversal (P2) does not touch JA: §3.2's sign display
  is anchored to tex 1431/1201 directly and re-verified at source here —
  JA's r1 fix was the faithful one; the W2 §3.1 issue is that note's own.

## 5. Requirement 3: arc accounting at HEAD

* Note surfaces (header / §7.3 / §8) agree with each other at "counter
  0/2 CLEAN, rounds 1–2 = PE1/PE2, next = JA-PE3" — TRUE as of r2 and now
  one round behind HEAD by the arc convention (a clean pass edits
  nothing; the note has had no repair round since). The live counter sits
  in the ledger (`BRIDGE_ADJUDICATIONS_2026-07-30.md`): "JA PE3 CLEAN
  (counter 1/2) ... JA-PE4 = the acceptance pass", matching this
  dispatch. Round facts vs git re-verified: PE1 report 5e70442
  (2026-08-04), PE2 report 9040961, r2 = 5d95805 note-only, PE3 report
  c77ae6f (2026-08-07, CLEAN, 4 ungraded observations), orchestrator
  counter action a83c108. Convention-consistent; the stale "next = PE3"
  strings are round-stamped history, closable at the fold — observation
  n3, not a defect.
* PE3's observations adjudicated independently: (o1) the r2 /tmp probe
  stays unauditable-but-disclosed; every load-bearing figure now has a
  THIRD independent reproduction (§3 P-E). (o2) census-scope wording —
  recoverable, stands. (o3) the [ILN]† as-of pin debt — now aged another
  round, still recorded fold-owed in the ledger; FINDING 1 is the same
  genre made material (the unpinned W-2 cite), which strengthens the case
  for executing the pin sweep at the repair. (o4) WM-companion present
  tense — WM r4 landed; fold-owed pointer stands.

---

## FINDINGS (0 critical, 1 justification gap, 0 minor)

* **FINDING 1 — GAP (W-2 supplier drift over the unpinned consumption;
  §2 cl. 8, §4 two bullets, §7.2 two rows).** As §4 above: the carried
  W-2 conditionality list is missing the supplier's post-JA-r2 mandatory
  item (d) (W2-OPEN-2 / OPEN-2a / proved-to-first-twist split / C1a
  qualifier), and the displayed W2-C3 grade text ("strictly at every
  level", "machine 44/44/44", "44/44") is struck in the supplier's own
  claims table at HEAD. One-bracket cure + as-of pin.

**Ungraded observations:** (n1) §5's GRB cite "REV 11/14" is dated (GRB
now carries REV 13/pass-16 brackets); consumed claims unaffected at
source — fold-sweep candidate alongside the pin debt. (n2) JA-VDIND's
sufficiency parenthetical "or ord(z_{m−1}) | A_{m−1} and the abscissa
condition" is ambiguous — under either parse it states a TRUE sufficient
condition (ord | A alone already suffices; the extra conjunct is
redundant, not false). (n3) arc surfaces one round behind at HEAD by
convention (§5). (n4) in the committed pools every root-character-visible
scored sample has (VD-m) FALSE (no cancellation instance realized) — the
unsealed-converse fence is doing no work on this roster, consistent with
"generically nonzero".

**What survived this hostile pass (for the record):** the per-slot gauge
law re-derived by a route none of PE1–PE3 used (ν-shift + W2-L2
covariance; symbolic identities proved by exact grid interpolation);
JA-VDIND's full triviality theory re-derived from the conjugation form
with four previously machine-unkeyed displays now instance-verified
396/396 (full form, difference display, JA-MIN support tie, packing) and
the single-slot surviving-constant claim exact on all 44 instances; the
witness census reproduced a third time (66 = 58+8, 66/66 root-visible,
330/0 on the trivial side); both JB pin quotes byte-true; 16 tex anchors
re-verified; §7 tables exact against the committed JSON; machine bracket
bit-identical with all seals intact at pins and worktree; arc accounting
convention-consistent.

JA-PE4 FINDINGS: 0 critical, 1 justification gap, 0 minor
VERDICT: NOT CLEAN — the counter resets (0/2; orchestrator's ledger
action); the gap is a one-bracket + as-of-pin repair (FINDING 1 cure),
after which the next pass is the acceptance attempt again.
