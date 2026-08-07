# GRTJA pass PE8 — eighth hostile pass (THE would-be accepting attempt at 1/2, post-r5, post-PE7-CLEAN) on GRTJA_PROOF_2026-08-08.md

**Verifier:** JA-PE8 (fresh hostile Fable context; fixes nothing). The
would-be accepting attempt: the counter stands at 1/2 (PE7 CLEAN, ledger
line "JA 1/2"); a clean pass here is the second consecutive — acceptance
(the counter action and the fold are the orchestrator's). The bar is the
same bar as every pass.

**Target pin:** note at HEAD (repo HEAD adc6cf3), md5 `cba309ce` ==
`git show f131c53:` (the JA-r5 repair commit — the note's last commit;
no uncommitted drift; `git diff f131c53 HEAD` over the note EMPTY, so
the text PE7 passed clean is byte-identical to the text graded here).
Artifact seals verified by md5 at worktree AND pins: runner
`grt_ja_checks.py` `5972d412` == @696eae8 (SEAL); output `0d6d0522` and
JSON `13ab52ab` == @1cbf8ca (VERDICT); `ja_pe6_lean_leg.lean`
`52a81e63` == @9dfd8fc. Supplier state at HEAD:
`GRTW2_PROOF_2026-08-08.md` last commit = **adc6cf3** (16:23:39, the
★ACCEPTANCE RECORD★ — W2 ACCEPTED 2/2, a PURE APPEND after 94534df: my
own diff shows +23 lines at EOF and NOTHING else, so every surface JA
pins/quotes is byte-unchanged through the acceptance); ITERLAWN and JB
last moved at the fold 5054d69 (15:10, post-r5; adjudicated below);
blueprint (00ce2b6), completion tree (46e583e), `grt_weld_probe.py`,
`iterlawn_pe_reimpl.py` motion-free.

**Charge executed:** (1) the machine leg re-run in a /tmp sandbox with
every census recounted from the committed JSON by own arithmetic (§1);
(2) statement-level truth of the four theorem displays + JA-PIN + the
honest boxes at HEAD, with the tex anchors re-read at source (§2);
(3) the pin system re-verified at all four pins, and the post-r5/post-PE7
supplier motion adjudicated (§3); (4) the arc system at HEAD after seven
passes, every round fact against git (§4); (5) TWO components re-derived
by TWO routes unused across all seven prior reports — the
GENERATING-FUNCTION route and the GALOIS-DESCENT route, the exact two
the route ledger had left (§5). PE7's five ungraded observations q1–q5
adjudicated independently (§6).

---

## 1. Machine leg — RE-RUN, BIT-IDENTICAL MOD TIMING

Re-ran `grt_ja_checks.py` (full battery, /tmp copy of the committed
artifact set; PARI leg live via cypari2): **exit 0, all 17 families
GREEN, TOTAL samples 10,311, 0 violations, CK-RES boundary 16, CK-BPREF
26, elapsed 5.4 s**; stdout 54/54 lines identical to the committed
output after stripping wall-clock fields (mechanical strip-compare: 0
mismatches); regenerated JSON deep-compared key-for-key against the
committed `grt_ja_checks_results.json`: **identical except `elapsed_s`**
(5.4 vs 7.4); `violations` empty in both. Censuses recounted from the
COMMITTED JSON by my own arithmetic: scored 443 (main 396 + QO 14 + d₀
33) = the CK-RES/CK-VDM samples cell; **boundary 16 = main 9 (T3B 4 +
I4B 5) + transported 7 (T3B 3 + I4B 4)**, every other row 0 — exactly
the two interior-twist towers, as §7.1 displays; **bpref 26 = 22 roster
hits on exactly 10 rows** (T2A/T2C/T2D/T2G 1 each, T3A/T3C/T3D 2 each,
T3E 4, T3F 1, I4C 7) **+ 4 d₀ hits** (JD5A/JD3A/JD3B/JD3C, 1 each);
family samples column == §7.1 cell-for-cell
(1/111/1,132/872/1,744/3,248/340/443/443/26/444/1,452/5/4/3/2/2);
TW-INST ledgers exactly 20; teeth per-row from the JSON `mut` records:
MJ-EPS 8/9/8 (T2A/T2B/T2D), MJ-VAL 11/11 (T2A/T2C), MJ-GRID 12/18
(T2A/T2B) — the §7.1 figures verbatim. BONUS: the rescued PE6 Lean leg
recompiled at HEAD — `lake env lean` exit 0, deprecation warnings only,
0 `sorry`, 18 root declarations + the docstring inventory intact.

## 2. Statement-level truth at HEAD — ALL FOUR DISPLAYS TRUE AS FENCED

Tex anchors re-read at source THIS pass (12 of them): tex 220/828/912
(slopes −h/e, h,e positive coprime) ✓; tex 449 (principal = negative
slopes) ✓; tex 829/882 (ψ monic irreducible ≠ y; F_r := F_{r−1}[y]/ψ) ✓;
tex 1149 ("never divisible by y") ✓; tex 1166–1168 (Prop `construct`
hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})) ✓; tex 1176 ("the greatest
side contained in L", initial point (s,u)) ✓; tex 1200–1201 (the
construct-child exponent (ℓ_{r−2}u_j − 𝔰_j)/e_{r−2}) ✓; tex 1028
(propertiesv) ✓; tex 1259 (vrphir: v_r(φ_r) = e_{r−1}f_{r−1}v_r(φ_{r−1}))
✓; tex 1285 (representative Def) ✓; tex 1291 (ℓ_rh_r − ℓ′_re_r = 1, "we
fix ℓ_r, ℓ′_r" — NO pinned representative, and the print's MINUS
convention vs the harness + convention, exactly the JA-BOX-3 territory)
✓; tex 1431–1438 (Def t(i), sign (s − ℓu)/e — OPPOSITE to 1200–1201, as
§3.2's SIGN CONVENTION display states) ✓; tex 1447/1497 (rescoeff /
defresidual, (s,u) = initial point of the ACTUAL side S, matching the
[JA-r1] tex-1498 correction) ✓; tex 1528–1541 (Lemma `enlarge` carries
(𝔰_i − ℓ_{r−1}u_i)/e_{r−1}) ✓.

* **JA-VAL (§3.1):** proof re-walked (base = both min coefficient
  valuation; step = shared keys ⟹ same canonical division, two identical
  integer min recursions, v_{m+2}(φ_{m+1}) = γ_{m+1} by clause 7); the
  shared-key fence and the GD-2 shear sentence displayed. CK-VAL
  1,132/0 re-ran. TRUE as fenced.
* **JA-EPS (§3.2):** the exponent identity re-derived by hand
  (ℓ′s − ℓu = (s(ℓ′e+ℓh) − ℓβ)/e = −t) AND by the fresh graded-uniqueness
  route (§5); the k-grid covariance re-derived (s(β+kW) = s(β) since
  e | W; t shifts by kA = kℓW/e); both signs re-checked at tex
  1200–1201 vs 1431–1438. TRUE.
* **JA-GRID (§3.3):** (a) + proviso re-derived from the abscissa GF
  (§5), counter-instance (2,3,1) ⟹ u = −1 reproduced; the [r1]/[r2]
  scoping brackets re-checked — the JB col-(b) quote re-verified
  byte-faithful at the 4c4ee56 pin (ellipses disclosed); (c) re-derived
  two fresh ways (GF defect; graded T-additivity). TRUE as fenced
  (single-level scope displayed).
* **JA-RES + JA-VDIND + (R-coll) (§3.4):** the per-slot exponent
  t(i) − τ = −iA re-derived (the shared attained abscissa cancels; the
  graded route gives it as the T-degree of x^{ℓiW}); the field step is
  one substitution under the proviso; the root-inclusive [r2] perimeter
  and the CK-VDM `triv` gate stand (443/0 re-ran); the conjugation-split
  display and BOTH JA-VDIND boundary clauses (single-slot NOT
  sufficient; converse NOT sealed) re-derived AND machine-witnessed by
  the descent probe (§5) — including, for the first time in this arc,
  CONSTRUCTED cancellation instances proving the converse fence
  non-vacuous in the field setting (PE4's n4 had noted none realize on
  the roster). TRUE as fenced. JA-MIN rides with its in(f)-leg-OPEN
  rescope; JA-BOX-1's refutation criterion re-derived (the ratio IS the
  character; ≥ 2 values ⟹ no slot-independent c) and the 26-witness
  census recounted.
* **JA-PIN (§2):** clauses 2–7 re-read against the anchors above
  (clause 5's one-liner checked: ψ(0) = 0 ⟹ y | ψ ⟹ ψ = y, excluded);
  clause 7's transcription re-checked against propertiesv/vrphir under
  P-index; clause 8 is consumption billing at its pins (§3). TRUE.
* **§4 transport:** ORB-EPS (t ↦ t + κβ), ORB-RES (z^{−κu₀}, z^{κh}
  rescale), and the §4(ii) (ξ,w) exponents (w-factor z^{−κ(β₀+s₀W̃)},
  ξ-factor z^{κ(γ_m−e_{m−1}W_{m−1})}) ALL re-derived from
  u_{i_j} = (β₀ + s₀W̃) + j(e·W̃ − γ) and machine-confirmed by the
  descent probe's coboundary leg incl. the cocycle composition law.
  The two [JA-r3] grade brackets faithful at the pin (§3). TRUE.

## 3. Pin system — ALL FOUR PINS INTACT; POST-r5 SUPPLIER MOTION ALL FAVORABLE AND PIN-PROTECTED

* **[W2 @ ffa1e57]** (§2 clause 8, §7.2 rows): the W2-C3 claims-table
  row re-read at the pin — the carried grade text ("PROVED at attempt
  grade given §3–§4 up to and including each chamber's first ξ ≠ 1
  junction (38/44 …); MEASURED above it (6/44: T3A/T3C/T3D/T3E r = 4,
  I4C r = 4,5) riding W2-OPEN-2", "machine TW-RATIO/TW-ADM 44/44
  (TW-STRICT SAME-adjacent)", "36 fully derived + 2 instance-warranted
  I4A/I4B r = 5") is at the pin verbatim; the §6.3 (a)–(d) carry-list
  re-read at the pin — (a)/(b)/(c)/(d) incl. the [r2, P1] (OPEN-2a)
  clause, all carried faithfully in clause 8.
* **[W2 @ 94534df]** (the [JA-r5] bracket): BOTH quotes re-verified
  byte-exact at the pin by own extraction — the W2-C3 row's [r3]
  FORWARD-direction-only bracket (pin line 980) and §6.3(d)'s
  [r4, PE4-P1] re-scope (pin lines 1005–1010).
* **[ILN @ ced7dbb]** (§1 harness): S0.1 and S0.2 — everything JA
  consumes — **byte-IDENTICAL between ced7dbb and HEAD** (own section
  extraction and compare: True/True), through the fold annex.
* **[JB @ 4c4ee56]** (§3.3): the col-(b) spans ("CARRIED AND
  UNDISCHARGED (r2, G2-5 …)", "[r5, F-3 — STATUS NARROWED …]") verbatim
  at the pin; the post-pin JB motion is the two fold errata — E-1
  ADOPTS JA's root-inclusive (R-coll) reading, E-2 defers W2-C3 grade
  cites to supplier HEAD — both pointing AWAY from any JA conflict.
* **Post-PE7 motion (new since the last report):** W2 was ACCEPTED at
  adc6cf3 (16:23) — a pure append (own diff 94534df→adc6cf3: +23-line
  acceptance record at EOF, nothing else). Every W-2 surface JA pins,
  quotes, or carries is byte-unchanged; the direction is strictly
  favorable (JA consumes clause 8 / W2-L0/L2/L3 / the §4 transport AT
  ATTEMPT GRADE from a supplier that now holds ACCEPTED grade at the
  same fenced scope — under-consumption, conservative). No re-quote is
  OWED at this pass: no JA repair round has occurred since r5, and the
  PE4-n3 convention (enforced by PE5/PE6/PE7) lapses deferrals only
  when a repair edits the note. See observation s1 for what the next
  repair/fold owes.

## 4. Arc system at HEAD — CONSISTENT AND TRUE UNDER THE FREEZE CONVENTION

Round facts vs git ALL EXACT: PE1 5e70442 (2026-08-04 22:42) → r1
ce0469a → PE2 9040961 → r2 5d95805 (19:36:43) → PE3 c77ae6f (CLEAN, 1/2
at a83c108) → PE4 535e79f (0C+1G, reset) → r3 8ee86da → PE5 6a216b9
(0C+1Gm) → r4 debf99d (09:46:49) → PE6 8b2fbed (0C+2Gm) → r5 f131c53
(14:47:46) → PE7 1670f67 (16:08:55, CLEAN). Cross-supplier timeline
facts re-verified: W2 r1 8d5e3fa 19:45:29 (8m46s ≈ "nine minutes" after
JA r2) ✓; W2 r3 79d1d9c 09:31:14, 15 min before r4 ✓; a48c22d 09:44:33
✓; W2 r4 94534df 14:20:00 ✓; fold 5054d69 15:10:55 ✓; W2 acceptance
adc6cf3 16:23:39 ✓. Live surfaces: the note is FROZEN since r5 (PE7 was
CLEAN — no repair round), so header/§7.3/§8 correctly read as-of r5
("rounds 1–6, counter 0/2, next = PE7") under the freeze convention the
campaign already exercised at W2's acceptance (S-STATUS as-of-r4); the
LIVE counter surface is the ledger, whose current line reads **"JA
1/2"** (BRIDGE_ADJUDICATIONS line 11820) — true. §8's heading "(rounds
1–6)" matches its contents; the r5 record's figures re-checked against
the PE7 report (verdict 0C/0G/0m CLEAN; machine figures; the [JA-r5]
quote inventory). **Fired-trigger sweep at HEAD:** every live deferral
checked against git — the fired triggers are ALL post-r5 (fold 15:10;
W2 PE5 CLEAN 15:03; W2 PE6 CLEAN + acceptance 16:23), no JA repair
round since, convention holds; inventory in observation s1.

## 5. Fresh legs: TWO components, TWO routes unused by PE1–PE7

Prior route ledger: PE1 field-identity subtraction + hand instances;
PE2 witness construction + sealed-engine probe; PE3 recursion-tree walk
+ QO/d₀ vein; PE4 ν-shift/covariance + grid interpolation + conjugation
probe; PE5 coset master lemma + engine-free Euclid; PE6 the Lean
kernel; PE7 unimodular-matrix change-of-basis (with a ℤ[x]/(x^e−1)
group-algebra leg that KILLS the carry marker). The two named remaining
routes, both executed here:

**COMPONENT 1 — the §3.2/§3.3/§3.4-integer/§4 exponent system by the
GENERATING-FUNCTION route** (`ja_pe8_gf_probe.py`, /tmp, md5 `a6abcbd3`,
disclosed uncommitted; NO repo import, NO pools; Bézout technology #4 —
EULER'S THEOREM ℓ := h^{φ(e)−1} mod e with own trial-division totient —
after the arc's modinv/pow, iterative-Euclid, and brute-scan
technologies). Derivations, each carried to the note's displayed form:
(GF-1) the on-line abscissa set 𝒜(V) = {a ≥ 0 : e | V − ah} has RATIONAL
GF x^{s(V)}/(1−x^e) — so s(V) = ord_{x=0} is an ℓ-FREE characterization,
u = (V − sh)/e ∈ ℤ automatic, u ≥ 0 ⟺ sh ≤ V (JA-GRID(a) + the
proviso's exact content); (GF-2) the carry is a GF DEFECT:
(1−x^e)·G_V·G_{V′} = x^{eδ}·G_{V+V′}, δ ∈ {0,1}, δ = 1 ⟺ s+s′ ≥ e
(JA-GRID(c) in one series identity); (GF-3) the graded carry-marker
algebra ℤ[x,T,T⁻¹]/(x^e − T) — the GF refinement that TRACKS the
overflow PE7's leg killed: x^{ℓV} = T^{t(V)}x^{s(V)} by unique normal
form, whence t-additivity t(V+V′) = t(V)+t(V′)+δ; **JA-EPS from graded
UNIQUENESS** (x^{ℓsh} = T^{−ℓ′s}x^s from ℓh = 1−ℓ′e, so
x^{ℓV} = T^{ℓu−ℓ′s}x^s ⟹ ℓ′s − ℓu = −t — no fraction subtraction, no
matrix); W2-L2 covariance from x^{ℓkW} = T^{kA} (e | W forces s
invariant, t ↦ t + kA, negative k included); the JA-RES per-slot
exponent as the T-degree of x^{ℓiW} (the shared attained abscissa
cancels, ANY representative of its residue class); the conjugation
split i_jA = s₀A + j(eA). Machine: exhaustive box e,h ≤ 14 coprime ×
V ∈ −40..80 + 300 random reads (e,h ≤ 50, |V| ≤ 10⁷), k ∈ −3..3 —
**385,057 checks, 0 violations, exit 0**; the (2,3,1) ⟹ (s,u) = (1,−1)
counter-instance reproduced.

**COMPONENT 2 — the §3.4/§4 FIELD-level twist system by the
GALOIS-DESCENT route** (`ja_pe8_galois_probe.py`, /tmp, md5 `191cc521`,
disclosed uncommitted; own field arithmetic incl. an 𝔽₂₅ =
𝔽₅[w]/(w²−2) extension leg — no repo import, no sympy). Derivations:
(DESC-1) the substitution σ_ϑ: Q(y) ↦ Q(ϑy), ϑ = z^{−eA} of order d,
generates ℤ/d acting on L[y] with ISOTYPIC DECOMPOSITION
L[y] = ⊕_c U_c (U_c = span{y^j : j ≡ c mod d}), eigenvector ⟺
single-class support, eigenvalue = ϑ^c, descends to invariants ⟺ c = 0
— both directions machine-checked; (DESC-2) the per-slot law data
assemble to R = z^{−s₀A}·σ_ϑ(Ĉ) — §3.4's conjugation-split display as a
μ_d-TORSOR statement (print residual and packed polynomial = one
element in two trivializations; the character is the cocycle);
(DESC-3) JA-VDIND forward BY DESCENT (absolute triviality on attained ⟹
R = Ĉ exactly), with BOTH boundary clauses: single-slot support = an
eigenvector whose constant z^{−i₀A} ≠ 1 SURVIVES (the note's "NOT
sufficient" clause, witnessed), and the converse NOT sealed —
**cancellation instances CONSTRUCTED (≥ 3 per field, all four fields):
character nontrivial on attained, R ≠ Ĉ as polynomials, evaluations at
z_m EQUAL** (the note's escape clause realized for the first time in
this arc); (DESC-4) JA-BOX-1's refutation criterion (χ takes ≥ 2 values
on attained ⟹ NO slot-independent c — the ratio IS the character);
(DESC-5) ORB-RES as a COBOUNDARY action κ ↦ (z^{−κu₀}, z^{κh}) on the
law orbit {c_j = wξ^jC_j}: orbit stability with the transported (w′,ξ′),
the cocycle composition law (κ₁ then κ₂ = κ₁+κ₂), and the §4(ii)
tower-coordinate exponents (z^{−κ(β₀+s₀W̃)}, z^{κ(γ−eW̃)}) from
u_{i_j} = (β₀+s₀W̃) + j(eW̃−γ). Machine: 𝔽₅/𝔽₇/𝔽₁₃/𝔽₂₅, 160 random
configurations each + the constructed-escape searches — **5,519 checks,
0 violations, exit 0**.

Between them the two probes re-derive: JA-EPS (statement + k-grid),
JA-GRID (a)+(c) with proviso, the JA-RES exponent + field step
consequences, JA-VDIND forward + both boundaries, JA-BOX-1's criterion,
and the FULL §4 transport — by mechanisms sharing no technology with
any prior pass.

## 6. PE7's five ungraded observations, adjudicated independently

q1/q2 (fold + W2-counter staleness): CONFIRMED and EXTENDED — see s1;
still observation-grade (convention + favorable direction + pins).
q3 (clause-8 (d) two-sided live text, rider in §8): CONFIRMED as
placement only — the carried package (pin-faithful text + §8 reading
rider) is faithful; ungraded. q4 (unpinned blueprint/completion-tree
cites): both motion-free at MY HEAD (00ce2b6/46e583e) — standing,
nil-weight. q5 (probe sealing offer): now three uncommitted fresh legs
(PE7 matrix `8fd286d0`, PE8 GF `a6abcbd3`, PE8 descent `191cc521`) —
orchestrator's option, nil-weight.

---

## FINDINGS: NONE (0 critical, 0 justification gaps, 0 minor)

**Ungraded observations (recorded, not graded):**

* (s1) **The fold-executable bracket inventory, grown since PE7:** the
  post-r5 fired triggers now include W2's ACCEPTANCE (adc6cf3). At the
  next repair round or fold, the note owes dated brackets at: §1's
  "ITERLAWN_PROOF motion-free since" (ILN moved at 5054d69 —
  append-only; S0.1/S0.2 byte-identical, verified); §5's W-2 bullet
  "(0/2 hostile passes)" and the grade-cap/§7.3 "attempt grade" billing
  (supplier now ACCEPTED at the same fenced scope — favorable, JA
  under-consumes); §3.2's "cure owed to that note's own arc" (W-2's arc
  CLOSED at acceptance with the inherited 1213–1218 range STILL
  standing in its §3.1 at HEAD — the factual "stands" claim remains
  true, but the named cure path no longer exists; the debt moves to
  erratum/fold genre); and PE7's q3 pointer. None of these misstate
  anything at their pins; all are the PE6-FINDING-2 species IF a future
  repair skips them.
* (s2) The freeze convention leaves the frozen header/§7.3 reading
  "counter 0/2 … next = PE7" while the ledger (the live surface) reads
  1/2 — consistent with the campaign's acceptance precedent (W2
  S-STATUS as-of-r4); the acceptance fold should stamp the note the
  same way W2's was stamped.
* (s3) The descent probe's constructed cancellation instances (DESC-3)
  positively witness the JA-VDIND converse-escape fence off the roster
  — complements PE4 n4 (no cancellation realizes ON the roster);
  corroborative, nil-weight.
* (s4) Standing nil-weight items ride: GRB dated-REV cite (PE4 n1),
  §7.3 short-form [r5] bracket (PE6 p1), blueprint/completion-tree
  cites commit-unpinned (PE5 m3).

**What survived this hostile pass (for the record):** the frozen text
byte-identical to what PE7 passed (md5 cba309ce == f131c53, diff to
HEAD empty); the machine bracket bit-identical (exit 0, 17 families,
10,311/0, boundary 16 = 9+7 on T3B/I4B only, bpref 26 = 22-on-10 + 4,
teeth 8/9/8, 11/11, 12/18) with seals 5972d412/0d6d0522/13ab52ab intact
at pins and worktree and every census recounted from the committed
JSON; the PE6 Lean leg recompiled exit 0 zero-sorry at HEAD; 12 tex
anchors re-read at source incl. both sign anchors (1200–1201 vs
1431–1438) and the unpinned-ℓ anchor (1291, with its minus-convention);
all four pins re-verified byte-exact ([W2 @ ffa1e57] grade text +
(a)–(d) carry-list, [W2 @ 94534df] both [JA-r5] quotes at lines
980/1005–1010, [ILN @ ced7dbb] S0.1/S0.2 byte-identical to HEAD,
[JB @ 4c4ee56] col-(b) spans with the fold errata E-1/E-2 pointing away
from conflict); the W2 acceptance verified a PURE APPEND (nothing JA
quotes moved; direction favorable); the arc system true at every live
surface under the freeze convention with all round facts and five
cross-supplier timestamps exact against git and the ledger at "JA 1/2";
and the exponent-and-twist system re-derived TWICE by the two remaining
routes — generating-function (rational abscissa GF + graded
carry-marker normal form; 385,057 checks / 0) and Galois-descent
(isotypic decomposition + torsor split + coboundary transport; 5,519
checks / 0 over four fields incl. 𝔽₂₅) — with the JA-VDIND boundary
fences positively witnessed on both sides.

JA-PE8 FINDINGS: 0 critical, 0 justification gaps, 0 minor
VERDICT: **CLEAN — the SECOND consecutive clean pass on the frozen
post-r5 text (PE7 + PE8). The 2-of-2 bar is met; the note is ACCEPTED
at its displayed grades** (counter action 1/2 → 2/2, the acceptance
stamp, and the s1 fold-bracket inventory are the orchestrator's ledger
actions). Observations s1–s4 name what the acceptance fold owes; no
repair is owed.
