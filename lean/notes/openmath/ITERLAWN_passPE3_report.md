# ITERLAWN pass PE3 — Fable round-3 hostile pass on the re-amended general-n note @ ea125e3

**FINDINGS: 0 critical, 1 gap (+1 nit); VERDICT: NOT-CLEAN (0C/1G).**
**Errata-r2 fidelity: VERIFIED — exactly the two brackets, purely additive;
the E4 row-2 EXP-KIT correction independently re-derived RIGHT; the (★)
count correction independently re-derived RIGHT from the artifacts' own
counting semantics. Re-runs: BOTH byte-exact (md5-identical to the frozen
outputs; exit 0; reimpl 0 violations + mutations 7/7 caught; diag 5,311
family-checks / 0 violations). The one gap is NOT errata-introduced: it is
original-composition text in the S7 failure-propagation display's
[IL3]-failure branch (present since 5fe901e, unexamined by all four prior
passes — checked against the PE/PE2/PC2 reports after my own read): the
branch lists REALIZE (#3) among the rows "NOT affected ... (they consume
only [IL] and this note's generic proofs)", contradicted by the note's own
S4.1 operative consumption bracket, its own S7 table row 3, and its own E4
bracket's row-3 sentence. Same genre, severity, and one-clause cure shape
as PE2-F1. Consequence: PC2 CLEAN + PE3 NOT-CLEAN on the same ea125e3 text
→ the 2-clean model-diverse bar is NOT met this round; acceptance does not
land; errata round 3 (one clause) then a fresh dual round owed.**

Verifier: Fable (ITERLAWN-PE3), fresh context, wallclock 2026-08-03
(campaign 2026-08-08). Target: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md`
at ea125e3 (1,293 lines; working tree at HEAD c4d841c is md5-identical to the
ea125e3 blob: b52d78631028e2eece0b55a9f9ba4bfa — PC2's commit touched only its
own report, so PC2 and PE3 ran on byte-identical text). Own full read FIRST;
prior reports (PE @ e7e9151, PE2 @ 5cd9b18, PC2 @ c4d841c) opened only after
my content view was formed.

---

## 1. ERRATA-r2 FIDELITY (charge 1) — VERIFIED, both brackets RIGHT

`git diff 5cd9b18..ea125e3` touches exactly 2 files: the note (+16/−2 lines,
both hunks bracket-ADDITIVE — each hunk's `−` lines are reproduced verbatim
inside its `+` lines, flawed text preserved per the errata discipline) and
the ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md` (+16, pure append: the r2
entry — content checked against the actual r2 actions, accurate, including
the PE2-N2 "head + 9 vs 10" corrigendum-of-record).

### 1.1 Bracket 1 — the (★) count correction (S2, after the PE-N2 note)

Claim: the diag's (★) coverage is **1,008 counter rows / 3,568 pair-levels**;
3,444 is the PE-reimpl's own count. Independently re-verified from the
artifacts' counting semantics (not from any report):

* `iterlawn_diag.py` fires `note("A2_star")` ONCE per pair then loops j=3,2,1
  (source :500–503), and `note("B4_star")` once per pair then loops j=4..1
  (:374–379). Output: A2_star 464, B4_star 544 → counter rows 464 + 544 =
  **1,008** ✓; pair-levels actually tested 464·3 + 544·4 = 1,392 + 2,176 =
  **3,568** ✓.
* `iterlawn_pe_reimpl_output.txt` TOTALS: `K3_star 3444` ✓ — and K3_star
  counts per pair-level (per-instance values = pairs × levels: I4A 144·3 =
  432, I5A 144·4 = 576, I6S 36·5 = 180, …, summing 3,444), so "3,444 …
  correct as stated for that leg" ✓.

The bracket is RIGHT; the never-tight observation and mechanism derivation
are untouched by the relabel. Nano-observation (no cure needed): none — the
bracket's arithmetic and attribution are exact.

### 1.2 Bracket 2 — the E4 row-2 EXP-KIT correction (S7, inside the r1 E4 bracket)

Charge question 1: do EXP-KIT's (b)/(c) cite [IL S2 L1]? **YES — verified in
the note's own S3 proofs:** (b) EPS-MULT: "substitute s(β+β′) =
s(β)+s(β′)−δe **(L1)**" (line 428); (c) EXP-SHIFT: "substitute **L1** and
ℓ(β″−β−β′) = ℓT" (line 435). And L1 is [IL]-owned by S2's own declaration:
"∎ (Consumed; the two-line proof is in [IL S2].)" (line 323). (a) EPS-CLOSED
is L1-free (pure Bézout/eq12 algebra — re-derived: s − ℓβ = e(ℓ′s − ℓu)).
S3's closing parenthetical concedes the scoping: "self-contained modulo the
ACCEPTED [IL] alone" (lines 439–440).

Charge question 2: does row 2 then recover exactly as row 1 does? **YES:**
row 1's sole [IL] consumption is EQ12-ADD, and rows 1 AND 2 both recover by
independently re-deriving that two-line elementary lemma (EXP-KIT(a) and the
kernel STATEMENTS are L1-free, so nothing else in row 2 falls). The bracket
says exactly this ("both recover by independently re-deriving the two-line
elementary EQ12-ADD lemma"). **Correction RIGHT.**

"Row 3's status stands as written" — also RIGHT for the E4 ([IL]-failure)
branch: row 3's dependencies (S0.2 base facts + [IL3]†'s m = 1 displays) are
[IL]-free at this note's level. (Row 3 in the OTHER failure branch is the
§3 finding.)

Nano-observation (no cure needed): the bracket's inline quote renders S3's
bare token as "[IL]†" where the S3 byte text is bare "[IL]"; under the §0
incorporation convention every bare [IL] token "is henceforth read as the
dagger form", so the rendering is the declared reading, not a misquote.

## 2. EXECUTION (charge 2) — both re-runs BYTE-EXACT

Referee mapping first: neither r2 bracket touches testable semantics —
bracket 1 relabels a count in a prose note (no predicate), bracket 2 edits a
hypothetical failure branch (no predicate). No check family in
`iterlawn_pe_reimpl.py` (K1–K15 + censuses + mutation battery) or
`iterlawn_diag.py` (A1–A5, B1–B7) maps to either bracket. Byte-exact re-runs
were therefore the sealed expectation — and held:

    iterlawn_pe_reimpl.py  re-run exit 0; output md5
      cfad79439821551f9c6a572f5d627d0b  = frozen iterlawn_pe_reimpl_output.txt ✓
      (script md5 cae45db2318b89520dd5484466ef3604 = PE-r1 seal ✓)
      actuals: 9 fresh instances (4/5/6 reads), 940 pairs; baseline
      violations = 0; K1_shift 3444, K2_dint 940, K3_star 3444, K4_window
      940, K5_l6 940, K6_wmult 940, K7_law 940, K8_pds 3421, K9_case 2490,
      K10_sharp2 940, K13_pass 1320, K15_tie/valtie 244/244, …;
      mutation battery 7/7 caught+visible; REIMPL VERDICT: CLEAN.
    iterlawn_diag.py       re-run exit 0; output md5
      7c72c4c6c0a953ebd41a56eab1e266e1  = frozen iterlawn_diag_output.txt ✓
      (script md5 cd7581b7fd9df555e517b69556199ef3 — both md5s match the
      note's S8 citations verbatim ✓)
      actuals: 5,311 family-checks (sum of the COUNTS block) / 0 violations;
      A1_casc 464, A2_star 464, A3_rho 36, A4_dcx_law 35, A5_e1pass 144,
      B1_L6 56, B2/B2'/B3/B4 544 each, B4_star 544, B5 224+24+56,
      B6_topcontrol 128, passthroughs 416+128+416 = 960; T5B censuses 16
      sharp-DCX₂/48 outer per instance, T5C 4 outer/0 sharp;
      DIAG VERDICT: CLEAN.

Every S8 display in the note re-checked against the output line-by-line: all
18 count rows match exactly.

## 3. FRESH FULL CONTENT SWEEP (charge 3) — one finding, one nit

### 3.1 PE3-F1 [GAP — narrow, display-grade, NOT errata-introduced]: the S7 [IL3]-failure branch's row list is false at row #3

The failure-propagation paragraph (S7, lines 1131–1135) displays the
[IL3]-failure branch:

> "if the [IL3] round-2 arc does NOT close clean, the rung-2 link re-opens
> and every rung ≥ 2 row of #5/#6/#8 falls back to 'open at the rung-2
> link' — the integer layer (#1), EXP-KIT (#2), REALIZE (#3), and the L6
> chain (#4) are NOT affected **(they consume only [IL] and this note's
> generic proofs)**."

The bolded parenthetical — the operative justification — is FALSE for row
#3 (REALIZE/WELL-DEF/READ-ADD), by the note's own displays, three ways:

1. **S4.1's operative consumption bracket** (lines 513–516, added at errata
   r1 as PE-G2's "one substantive flagged site"): "the m = 1 base legs of
   REALIZE-(m)/WELL-DEF-(n) above **consume [IL3] WELL-DEF(i)/(ii)**" —
   and the S4.1 proof body: "m = 1 is [IL3] WELL-DEF(i)'s display",
   "(At m = 1 this is [IL3] WELL-DEF(ii) verbatim.)".
2. **The S7 ledger table itself** (line 1121): row 3's rung-2 cell reads
   "**[IL3] + S4.1**" — and the r38 bracket confirms ("row 3 rung-2
   likewise reads accepted + S4.1").
3. **The adjacent E4 bracket's own row-3 sentence** (lines 1163–1164):
   "Row 3 (REALIZE/WELL-DEF/READ-ADD) rides only the S0.2 elementary base
   facts **and [IL3]†'s m = 1 displays**."

So under the branch's hypothetical (the [IL3] arc does not close clean —
[IL3] stays at attempt grade or is withdrawn), row #3 IS affected: its
m = 1 base legs revert to consuming an unaccepted artifact, i.e. row 3
falls back to "open at the [IL3] WELL-DEF(i)/(ii) m = 1 displays"
(elementary realize-constructions, independently re-derivable — S4.1's own
parenthetical already re-derives the (I₁) admissibility bridge inline; the
recovery is the same genre as rows 1–2's open-at-L1). Rows #1/#2/#4 are
genuinely [IL3]-free (#1: L1 only; #2: L1 only, per the r2-corrected E4
bracket; #4: [IL] base only) — the parenthetical is false for exactly one
of the four listed rows.

**Failure scenario:** a reader pricing an [IL3]-failure recovery off this
display treats rows #1–#4 as [IL3]-free and re-derives nothing at S4.1,
leaving REALIZE's m = 1 base (hence every canonical lift, hence WELL-DEF
and both II-leg Ĉ-objects) resting on a withdrawn artifact with no flagged
fallback. No live claim is broken — [IL3] is in fact ACCEPTED (r38
bracket), the branch is counterfactual, and the ledger TABLE prices row 3
correctly — but the campaign's own standard (PE2-F1, cured at errata r2)
grades exactly this defect shape in the SAME display: a failure-branch
clause contradicting the note's own consumption record. Symmetry of
standards requires the same grade.

**Cure (one clause, the PE2-F1 shape):** amend the row list to "…and the
L6 chain (#4) are NOT affected (#1/#2/#4 consume only [IL] and this note's
generic proofs); REALIZE (#3) falls back to 'open at the [IL3]
WELL-DEF(i)/(ii) m = 1 displays' (elementary, independently re-derivable —
the S4.1 operative bracket's consumption)."

**Provenance of the miss:** the clause is original composition (present at
5fe901e, before errata r1 added the S4.1 bracket 600 lines above it).
Checked AFTER my own read: PE r1 examined the failure display only for
consumption-legality (its report line 254) and separately recorded "row 3
covers the S4.1 site" for the TABLE; PE2's §3.3 verified rows of the E4
([IL]-failure) branch only; PC2 verified "corrected EXP-KIT failure
propagation" (the E4 branch) and the ledger's consistency. None examined
the [IL3]-branch row list. Fresh-eyes finding, never adjudicated.

### 3.2 The clean remainder of the sweep (all hand-re-derived, no findings)

* **Statement + class pin (S0.1–S0.3):** recursion re-unrolled by hand at
  n = 1 (δ₂, S₁ = γ₂δ₂, D₁ — the [IL] display exactly) and n = 2 (δ₃, D₂,
  Σ = S₁, D₁ — the [IL3] display exactly, matching the S4.1/S7 pastes
  token-for-token); γ₁ = h₀ convention threads consistently (w_jΦ_j =
  e_{j−1}g_{j−1}γ_j for all j ≥ 1); E-positivity, Bézout normalization,
  (ITER-LAW-LIFT) propagation ✓.
* **Integer layer (S2):** SHIFT-(n) top + step re-derived including the
  Bézout conversion 1 − ℓγ_j = e(ℓ′ − ℓwΦ); the SHIFT⇄D-INT top-down
  interleave is genuinely non-circular (D_j-INT at j needs only SHIFT at
  j, already in hand); D_j-INT congruence s ≡ ℓβ (mod e) re-derived;
  (★)-POS both cases re-derived, active-case chain (g_{j−1}−1)e_{j−1}γ_j +
  γ_j + h_j/e_j > γ_j exact; WINDOW-(n) worst-case bookkeeping exact
  (S₁ > (e₀−1)h₀ kills the defect's worst case); slotwise cocycle
  telescoping ✓; ℤ/E_{n+1}-descent shift bookkeeping (Π_j) ✓.
* **EXP-KIT (S3):** (a)/(b)/(c) re-derived from scratch; dependency census
  is exactly {L1 in (b), L1 in (c)} — the §1.2 verification.
* **S4.0–S4.2:** TRUNC ✓; REALIZE-(m) invariant descent re-derived
  (k_i ≤ e_{m−1}g_{m−1}−1 → γ⁽ⁱ⁾ ≥ γ_m/e_{m−1} > e_{m−2}g_{m−2}γ_{m−1} =
  (I_{m−1})); slot-weight integrality checked; (R1) degree bound, (R2)/(R3)
  slotwise read-off ✓; WELL-DEF (I_m)-discharge γ_{m+1} > e_{m−1}g_{m−1}γ_m
  ✓; READ-ADD induction ✓; L6-(n) degree telescope (e_j−1 ≤ e_jg_j−1) and
  single-digit read ✓ — genuinely engine-free and DCX-free at every rung.
* **IH-package closure (the induction step):** (P-L6)/(P-WM)/(P-DS) at
  rung n re-checked clause-by-clause out of each of the four legs. Case I:
  w/grid/read arithmetic exact; exports E₀ⁿᵉʷ = A (certified read = the
  δ-product ✓), E₁ⁿᵉʷ = 0. II-1: slot-k line = B_n attained, slot-(k+1)
  line = B_n + h_{n−1} via the IDENTITY γ_n − e_{n−1}w_{n−1}Φ_{n−1} =
  h_{n−1} (no g_{n−2} hypothesis needed — checked, since II-1 doesn't
  carry CII_{n−1}); the ε′-carry/canonical-lift cancellation re-derived
  (EPS-MULT at level n−1 + τ_{n−1} = ε_{n−1}(γ_n)^{−1}c_{n−1} → C₀ =
  z_n^{δ}vε_{n−1}(B_{n−1}) exactly); top-level slot-(T+1) analysis exact
  including the e_n = 1 on-grid-strictly-above leg (B_n − γ_{n+1} <
  B_n − e_{n−1}γ_n ⟺ γ_{n+1} > e_{n−1}γ_n ✓). II-2: E₁ⁿᵉʷ weight clause
  propagates with h_{n−1} to spare (g_{n−2} = 1 legitimately available via
  E₁ᴵᴴ ≠ 0 ⟹ CII_{n−1}); R¹ line = B_n + h_{n−1} and Q¹ line = B_n +
  2h_{n−1} re-derived; the k+2 ≤ e_{n−1}−1 ⟹ e_{n−1} ≥ 3 vacuity ✓; the
  e_{n−1} = 2 collision impossibility (Q¹ = 0 off-DCX) ✓. II-3: all three
  slot lines re-derived including both r1 brackets (PC-G4's Q¹ bound: line
  − B_n = 2h_{n−1} exact; PE-N1's E₁-export display: = B_n − e_{n−1}γ_n +
  h_{n−1} exact); both collision legs (e_{n−1} ∈ {1,2}) READ-ADD-killed ✓;
  E₁ⁿᵉʷ top line = Γ″ + h_n + e_nh_{n−1} re-derived. S5 assembly: one
  EXP-KIT(c) kernel per level with T = S_j, D_j exactly the recursion's,
  δ_j^{pl}-carries cancel in-kernel ✓.
* **T-notation layer (spot-check, 11 tokens of my choosing):** S4.4 support
  bracket; "S_n+1 ≤ 2e_{n−1}−1" (line 676); "S_n ≤ e_{n−1}−2" (677); II-3's
  "S_n = e_{n−1}−1" (680); II-1's "Φ_{n−1}^{S_n}" (787) and "s_n(B_n) =
  S_n − e_{n−1}" (803); the slot-line identity "e_{n−1}B_{n−1} + S_nγ_n =
  B_n" (798); II-2's "Φ_{n−1}^{S_n+1}" (828); the Φ_n-exponents
  "S_{n+1}/S_{n+1}+1" (790/831); S4.7's "S_m ≤ 2e_{m−1}−2" (936); the
  (P-DS) support display (616–617). Each is TRUE under the raw-sum reading
  and false or ill-typed under the composed one; no composed S_j occurs
  anywhere in S4.3–S4.7; no site consumes one reading while asserting the
  other. The byte-frozen [IL3]† pastes retain [IL3]'s own S₁ as declared ✓.
* **(RM-m) boxing:** no PROVED leg silently consumes an unboxed engine —
  S2/S3/S4.0/S4.1/S4.2/S4.5 are engine-free by construction (re-checked);
  the II legs and the S4.7 outer bound display their (RM-(n−1)) / IH-(P-DS)
  consumption; RM-1's open corner {e₀ = 1 ∧ d₀ ≥ 2} is structurally dodged
  by the rung-2 step (e₀ = 1 ⟹ δ₁^{pl} = 0 ⟹ CII₁ false ⟹ Case I only,
  no engine call — re-derived); rung ≥ 3 steps consume RM-(n−1), n−1 ≥ 2,
  never RM-1 ✓.
* **DCX-(n) outer bound + qualifiers:** proof re-derived (Q⁰ emission needs
  T_m ≥ 2e_{m−1}−1, impossible; Q¹ needs CII_{m−1} + the extreme s-track);
  the PE-G1 "(given IH package)" qualifier present at all three sites
  (S0.3 bullet, S0.3 table row, S4.7 bracket) ✓; m = 2 sharp = [IL3];
  m ≥ 3 sharp honestly OPEN with the e_{m−2} ≥ 3 conjecture labeled
  CONJECTURED ✓.
* **Corollaries (S6):** COR-1..COR-5 re-checked (D_n = δ_n^{pl} collapse at
  e_n = 1; passthrough at interior e = 1; ρ = ∏ z_j^{−ℓ_{j−1}Π_{j−1}}
  re-derived from EXP-KIT(a), matching S8's A3 display); OFF-DCX qualifiers
  baked into every field-level clause; DCX non-evacuation displayed ✓.
* **Conditionality ledger + failure branches:** rows 1–11 re-checked
  against the body (row-by-row); the r38 bracket's upgrades fire correctly
  and only in the good direction; the E4 ([IL]-failure) branch as
  r2-amended is now RIGHT on all rows (rows 1/2 open-at-L1, row 3's
  [IL]-free dependency list, rows 4/5/6/8/10 total-loss chain re-derived);
  the [IL3]-failure branch = finding F1 above.
* **S8:** labeled NOT a proof step / instance evidence only at head and
  foot; all 18 count rows + censuses match the re-run output exactly;
  md5s in the note match the artifacts ✓.
* **Rule-8 under the incorporation convention:** §0 head declaration
  present with both defined-term blocks pasted in full; operative-site
  pastes at the S4.3 base paragraph ([IL]), S4.1 ([IL3]†), and the S7 r38
  bracket ([IL3] + [IL]) all present and byte-consistent with the header
  blocks; token census 41 [IL] / 71 [IL3] mentions — all non-paste sites
  covered by the declared dagger reading; the r2 brackets introduce no
  naked-token regression ([IL]† used; [IL S2 L1] is a compressed pointer
  under the convention) ✓.

### 3.3 Nit + nano-observations (no grade impact)

* **N1 [nit]:** S4.4's closing parenthetical "the union of Cases II-* is
  CII_n" over-claims: on the stratum {g_{n−1} = 1, E₁ᴵᴴ = 0, δ_n^{pl} = 0,
  CII_{n−1}, T_n = e_{n−1}−1} the pair is CII_n-positive but lands in
  Case I, so the union is strictly CONTAINED in CII_n in general. Only the
  ⊆ direction is ever consumed ((P-DS)'s "E₁ ≠ 0 ONLY in CII", and S4.7's
  E₁ᴵᴴ ≠ 0 ⟹ CII_{m−1}), so nothing downstream breaks. One-word cure
  ("is" → "lands inside").
* Nano: (★)-POS active case ends "e_{j−1}S_{j−1} > γ_j ≥ γ_j" — a display
  stutter (read: "> γ_j, hence ≥ γ_j"); the chain above it is exact.
* Nano: the r2 row-2 bracket's [IL]† rendering of S3's bare token — §1.2;
  convention-faithful, not a misquote.

## 4. CONSEQUENCE FOR THE ARC

PC2 (Codex) CLEAN + PE3 (Fable) NOT-CLEAN, both on the ea125e3 text → the
round is NOT double-clean; the 2-clean model-diverse bar is NOT met; the
general-n note is NOT accepted at this round. The mathematics of the
generic step again survived a full hand re-derivation and byte-exact
re-execution; the defect is one clause in a hypothetical display, cure
priced above (+ the optional N1 word). Counter: unchanged (no clean round
banked). Owed next: errata round 3 (orchestrator-direct, one clause), then
a fresh dual round on the amended text per the standing process.

## APPENDIX — provenance (tails eyeballed)

* HEAD at verification: c4d841c; target text = ea125e3 note blob, md5
  b52d78631028e2eece0b55a9f9ba4bfa (= working tree; PC2's commit ea125e3→
  c4d841c touched only ITERLAWN_passPC2_report.md, verified via diff
  --stat).
* Errata diff: `git diff 5cd9b18..ea125e3` = the note (2 additive bracket
  hunks at S2:387–392 and S7:1156–1163) + the ledger r2 append (+16 lines,
  tail-anchored at :8199–8215). No other file.
* Re-run 1: `python3 iterlawn_pe_reimpl.py` → exit 0, /tmp copy md5
  cfad79439821551f9c6a572f5d627d0b == frozen output. Tail eyeballed:
      M6  vis=8     viol=8     CAUGHT  rho monodromy exponent sign flip
      M7  vis=56    viol=56    CAUGHT  (P-DS) E1 weight bound tightened by +1
      == VERDICT: baseline violations = 0; mutations caught+visible = 7/7; elapsed 7.0s ==
      REIMPL VERDICT: CLEAN
* Re-run 2: `python3 iterlawn_diag.py` → exit 0, /tmp copy md5
  7c72c4c6c0a953ebd41a56eab1e266e1 == frozen output. Tail eyeballed:
      B6_e3pass: 416
      B6_topcontrol: 128
      == VIOLATIONS: 0 ==
      total elapsed 2.5s
      DIAG VERDICT: CLEAN
* Script md5s: iterlawn_diag.py cd7581b7fd9df555e517b69556199ef3,
  iterlawn_pe_reimpl.py cae45db2318b89520dd5484466ef3604 — both match the
  note's S8 / PE-r1 seals. `git status` on verification/openmath: no
  tracked-file modifications (re-runs wrote to /tmp only).
* Prior reports opened AFTER the fresh read: ITERLAWN_passPE_report.md,
  ITERLAWN_passPE2_report.md, ITERLAWN_passPC2_report.md — used only for
  §3.1's never-adjudicated check and grading calibration (PE2-F1).
* This pass commits ONLY this report + the ledger append (git commit
  --only); no push; the note itself is untouched.
