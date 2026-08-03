# ITERLAWN-PE5 — Fable round-5 hostile pass on the general-n note as amended at 0672082

## §0 VERDICT BLOCK

**Text verified:** `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` at 0672082,
md5 `5811db126d1ed0824e4870b20e0fd774` (matches the charge). Fresh verifier;
no prior contact with this arc.

**VERDICT: NOT-CLEAN — 0 critical / 1 gap (PE5-F1) / 0 nits.**

* **Errata-r4 fidelity: VERIFIED.** Character-level opcode check: the r4 diff
  on the note is **insertion-only** (8 insert spans, ZERO delete/replace
  opcodes), so all 5 diff-touched lines resume verbatim inside their
  extensions; the bridge-ledger append is 52/0. The row-4 correction was
  independently re-derived **RIGHT on both legs** (§2), incl. the rung-1
  exemption; the six expression sites are mutually coherent.
* **Re-runs: BOTH BYTE-IDENTICAL** to the committed artifacts (strictly
  stronger than PE4's content-identical: even the wall-clock digit coincided
  this run). reimpl 940 pairs / 0 baseline violations, 7/7 mutations caught;
  diag 5,311 family-checks / 0 violations. §3.
* **The sweep table, adversarially: ALL 12 purely-VERIFIED rows independently
  re-derived and CONFIRMED** (12/12, exceeding the ≥ 8 charge), plus the V
  legs of mixed rows 6, 12, 15, 20, 21. **No row falsified. Zero false
  dependency claims found anywhere** — the r4 sweep's substantive result is
  confirmed by a full independent pass. §4.
* **PE5-F1 [GAP — the r4 sweep's exhaustiveness sentence, S7 head]:** the
  genre-closing bracket's universal claims ("EVERY dependency/exemption claim
  in this note (grep patterns: … consume(s) …), each verified"; "zero
  unverified dependency claims remain") are **falsified by one in-scope,
  unenumerated claim-site**: the S0.3 statement-convention gloss "S₀ = D₁h₀ +
  S₁ℓ₀′ — computed by the recursion but **consumed by nothing**" (line
  207–208; display tag "[composed shift; S₀ unused]", line 201). In-scope by
  the sweep's own standards: the site matches the sweep's de facto "consumed"
  pattern (rows 3 and 15 quote "is consumed"/"ever consumed" sites), and it is
  exactly row 1's species (object-level non-consumption; row 1 = "the cocycle
  never consumes Φ_{n+1}", also a definitional-apparatus site). No prior pass
  verified it (grep over all five pass reports: the only S₀ mention anywhere
  is a token-census line in PE2's notation sweep). **The missed claim's
  content is TRUE** — verified this pass (§5): S₀ occurs nowhere in the note
  outside its two definitional sites; every downstream consumer of the
  composed shifts instantiates j ≥ 1 only (EXP-KIT kernels j = n..1, WINDOW's
  S₁, (★)-POS j = n..1). So this is a **content-true census leak**: no false
  dependency claim, no grade impact, no math impact. But the round-4 bracket
  reports an audit as complete under its own stated method while the method's
  scope contains a site the table does not — the same leak mechanism the
  bracket was written to certify against (rounds 2/3/4 each leaked one site;
  those leaked sites were false, this one is true). The ledger-side r4 block
  carries the same defect ("the genre has no remaining unverified surface").
  **Cure: one sweep row** (#23: S0.3 statement convention, "S₀ … consumed by
  nothing" — VERIFIED) + the census sentences restated (22 → 23); one clause
  in the bridge block.

**Round consequence:** the round-5 2-clean bar is NOT met regardless of PC4.
Owed: errata round 5 (one-row cure above), then a fresh dual round 6.
Severity, stated plainly for the adjudicator: this is the weakest finding of
the arc — the note's mathematics, all 22 existing sweep adjudications, both
failure branches, and both execution referees all stand confirmed; the sole
defect is the completeness sentence of the r4 audit bracket. A reasonable
purposive reading (scope = claims whose falsity could mis-grade a leg; S₀
carries no grade) would grade this a nit; I grade it a gap because the
bracket defines its scope by grep patterns, not by purpose, and the round-5
acceptance rides on precisely that sentence.

## §1 Charge and identity

ITERLAWN-PE5, Fable round-5 pass per the 0672082 commit message ("round 5
(PC4+PE5, both on this text) = the acceptance attempt"). Duties: (1)
errata-r4 fidelity; (2) adversarial re-derivation of ≥ 8 of the 12 purely
VERIFIED sweep rows; (3) execution re-runs; (4) fresh content sweep of the
standing surface; (5) this report + ledger + scoped commit. Both round-5
passes CLEAN = the note ACCEPTED; any finding = errata + fresh round.

## §2 Errata-r4 fidelity (VERIFIED; the correction re-derived RIGHT)

**Mechanical:** `git diff --numstat 4d0eeb1..0672082` = note 115+/5−, bridge
52+/0−. Character-level `difflib` opcodes on the full note text: kinds =
{equal, insert} only, 8 insert spans (+267 S0.3 L6 row, +355 S1 gloss, +1130
S4.2 close, +5563 sweep table, +190 S7 row 4, +237 nested r3-supersession,
+1514 branch-A r4 erratum, +550 DAG edge), **zero delete/replace** — the 5
diff-deleted lines are pure extensions with the original content resuming
verbatim (the ledger block's "0 lines deleted; 5 touched lines resume
verbatim" claim is exact). Base md5 of the 4e8f027 text confirmed
`c088101c9676118566a54ad3bb18dfdf` as the bridge block records.

**The row-4 correction, independently re-derived (both S4.1-consumption
legs):**

* **Telescope-input leg.** S4.2's degree telescope consumes deg Φ_{j+1} =
  e_jg_j·deg Φ_j (and Φ_{j+1} monic, for the next level's division
  algorithm). For j ≥ 1: Φ_{j+1} = Σ_{k ≤ g_j} C_kΦ_j^{e_jk}, C_{g_j} = 1.
  Top term: monic of degree e_jg_j·deg Φ_j. Lower terms (k < g_j):
  deg(C_kΦ_j^{e_jk}) < (1 + e_jk)·deg Φ_j ≤ (1 + e_j(g_j−1))·deg Φ_j ≤
  e_jg_j·deg Φ_j — where the first "<" is exactly (R1)'s deg C_k < deg Φ_j
  and the C_k must EXIST, i.e. WELL-DEF(i)'s certification that each
  realize_j entry weight (g_j−k)γ_{j+1} satisfies (I_j). (The e_j = 1 corner:
  1 + (g_j−1) = g_j, equality in the last step, strictness already supplied
  by (R1) — no leak.) So the telescope input IS an S4.1 export; a "free-
  standing arithmetic" reading is wrong, exactly as the erratum says.
* **Certification leg.** At rung n ≥ 2 the class's own towers carry canonical
  lifts Φ₂,…,Φ_n (construction range 1 ≤ m ≤ n−1), each defined through
  realize_m recursing down to realize₁ — S0.1's own pin: "well-definedness on
  the class: Lemma WELL-DEF-(n), S4.1". TRUNC's "identical … lifts" clause
  presupposes the same certification. And S4.1's m = 1 base legs consume
  [IL3]† WELL-DEF(i)/(ii) (the S4.1 operative bracket) — so under the
  [IL3]-failure hypothetical, row 4 falls WITH row 3 at rungs ≥ 2. RIGHT.
* **Rung-1 exemption RIGHT:** at n = 1 the construction range 1 ≤ m ≤ n−1 is
  empty (no canonical lift; Φ₁ = the standard lift), and the telescope's
  j = 0 leg (deg Φ₁ = e₀g₀d₀) is the standard-lift definition, [IL]-covered.
  L6-(1) = [IL S4 L6]. "Rung 1 given [IL] alone" is exact.

**Six-site coherence:** S0.3 L6 row, S1 item-1 gloss, S4.2 close bracket, S7
table row 4, branch-A r4 erratum (+ the nested supersession of the r3 "Rows
1/2/4 stand" clause), S10 DAG edge — all six state the same mechanism
((a) class-pin certification + (b) telescope input, m = 1 base on [IL3]†),
the same scope (rungs ≥ 2; rung 1 exempt where a rung-1 cell exists), and all
preserve the negative clause (no W-MULT / no RM / no DCX) — which I confirm
independently: L6-(n)'s proof-body consumption census is exactly {TRUNC,
telescope (S4.1), IH = L6-(n−1), [IL] base}; no W-MULT/RM/DCX object appears.
No contradiction among the six sites or with sweep rows 4/6/12/19/22.

## §3 Execution re-runs (both exit 0, both BYTE-IDENTICAL)

Script md5s match the note's pins: `iterlawn_diag.py` =
`cd7581b7fd9df555e517b69556199ef3` (S8 pin exact); `iterlawn_pe_reimpl.py` =
`cae45db2318b89520dd5484466ef3604` (the e7e9151-era referee, unchanged).

* **iterlawn_pe_reimpl.py:** exit 0; `== BASELINE VIOLATIONS: 0 ==`; pairs
  940; per-family totals byte-identical (K1_shift 3444, K3_star 3444,
  K7_law 940, K10_sharp2 940, …); mutations `7/7 caught+visible`. Fresh
  output md5 `cfad79439821551f9c6a572f5d627d0b` = committed
  `iterlawn_pe_reimpl_output.txt` **byte-identical**. PE4's benign wall-clock
  digit diff did NOT recur (elapsed coincided at 7.0s). Classification: no
  diff of any kind.
* **iterlawn_diag.py:** exit 0; fresh output md5
  `7c72c4c6c0a953ebd41a56eab1e266e1` = committed — **byte-identical**. Count
  block sums to exactly **5,311 / 0 violations**. Every S8 claim re-checked
  against the fresh output: A1/A2 464, A3_rho 36/36, A4 law-on-outer 35/35
  (outer census 28/0/7, sharp 0), A5 144; B1 56/56, B2/B2′/B3 544 each,
  B4 544+544, B5 224+24+56, B6 128 + passthroughs 416+128+416 = 960,
  B7 censuses T5B dcx2s 16 / outer 48 per instance, T5A 0, T5C 4/0. All
  match the note.

## §4 The sweep table, adversarially: all 12 purely-VERIFIED rows re-derived

Method: for each row, an independent re-derivation from the note's own text
(never from the row's adjudication column), with execution/grep legs where
the claim is mechanical. **Result: 12/12 CONFIRMED; none falsified.**

| row | claim | my independent re-derivation | verdict |
|---|---|---|---|
| 1 | S0.1: "the cocycle never consumes Φ_{n+1}" | grep: Φ_{n+1} occurs exactly twice in the note — the claim site and the sweep row quoting it. Construction range 1 ≤ m ≤ n−1 stops the lifts at Φ_n; anchors use Φ₀…Φ_n; val = R_{n+1}v runs Φ_m-developments for m ≤ n only | CONFIRMED |
| 2 | head: "consumes exactly two accepted defined-term blocks" | full external-citation census re-run: proof-grade = [IL]† (L1, L6 base, ITER-PKG-1, EXP instances) + [IL3]† (WELL-DEF(i)/(ii) m = 1, RM-1 = DIGIT-SPLIT+DEV-1, the r = 2 package, DCX₂ sharp form) and NOTHING else; harness code (grb :499–507, realize/build_PhiK) consumed as definitions; ITERLAWR/ITERLAW4/M2/M3/S8 evidence-only; L3CONVERGENCE/ITERLAWR-S6 statement-identity only | CONFIRMED |
| 3 | print-consumption display | every consumption site classifies as definition-consumption or accepted-lemma-consumption; S8 fenced "NOT a proof step"; no site derives anything from printed output or text extraction | CONFIRMED |
| 7 | S2: D_j-INT "needs only β_j″ = B_j + S_j" | re-derived: s(β) ≡ ℓβ (mod e) from β = eu+sh, ℓh+ℓ′e = 1; then defect + ℓ_{j−1}S_j ≡ ℓ_{j−1}(β_j+β_j′−β_j″+S_j) = 0 given SHIFT at j. Top-down interleave well-founded (no circularity) | CONFIRMED |
| 8 | S2 descent: constants depend only on (γ, γ′ mod E_{n+1}) | re-derived: +E_{n+1} fixes s_{n+1} and shifts β_n by Π_n; inductively fixes every s_j, shifts β_{j−1} by Π_{j−1}, u₁ by 1 — all defects, δ, D_j, S_j invariant; φ_{γ+E} = πφ_γ. Diag legs B5_pi 24/24, B5_descent 224/224 re-run | CONFIRMED |
| 9 | S3 close: "self-contained modulo [IL] alone" | (a) is pure Bézout algebra (ℓβ = ℓeu + (1−ℓ′e)s); (b) = (a) + L1; (c) = (a) + L1 + ℓT arithmetic. Sole external = L1 = [IL S2 L1] | CONFIRMED |
| 10 | TRUNC: lift construction at level m consumes only levels ≤ m | C_k input census: ψ_{m,k} ∈ K_m, γ_{m+1} = e_mw_mΦ_m + h_m (read-m data), ε_m, realize_m (recursion strictly downward through ε_{m−1}, Φ_{m−1}, eq12(·; e_{m−1},h_{m−1})), Φ_m — no level-(m+1) object; hence truncated tower's lifts ≡ full tower's | CONFIRMED |
| 13 | (P-L6): "[No DCX exclusion needed]" | L6-(n) is stated for every γ ∈ W_{n+1} (no DCX hypothesis); S4.1's lemmas carry none; the clause legitimately escapes the package's OFF-DCX quantifier | CONFIRMED |
| 14 | "composed shifts S_j NEVER appear in S4.3–S4.7" | mechanical token sweep of lines 589–993: every capital-S occurrence is (i) the r1 erratum's own gloss, (ii) an in-line-defined raw sum ((P-DS)'s S_{r+1}), or (iii) a raw-sum site under a dated r1 bracket; zero composed-shift semantics. Companion clause "the two layers meet only through B_j and δ_j^{pl}" re-verified at the S4.5/S4.6 → S5 interface. Code-referee leg: the reimpl implements ssum and S separately, 0 violations | CONFIRMED |
| 16 | "rung ≥ 3 steps never consume RM-1" | the step to rung n calls (RM-(n−1)) at exactly four sites (II-1 ×1, II-2 ×2, II-3 ×1), all at level n−1 ≥ 2 for n ≥ 3; RM-1 enters only inside the rung-2 package, consumed wholesale as [IL3]† (incl. the DCX₂ sharp form) | CONFIRMED |
| 17 | PE-G1 bracket: engine-free-support lemma "plausible, NOT claimed" | honest fence; checked no site consumes it as proved — both S0.3 display sites and the S4.7 head carry the "(given IH package)" qualifier | CONFIRMED |
| 18 | S6.1: "no cross-level denominator ever forms" | S5 re-derived: the j-th bracket z_j^{δ_j^{pl}}ε_j(B_j)/ε_j(β_j″) closes inside level j via EXP-KIT(c) at T = S_j with D_j ∈ ℤ; no denominator crosses levels. (Same claim also expressed at S1 item 3 and the S3 close — both true; folded into this row, noted §5) | CONFIRMED |

**Mixed-row V legs also re-derived (beyond the charge):** rows 6/12 negative
clauses (L6-(n) proof-body census = {TRUNC, S4.1 telescope, IH, [IL] base} —
no W-MULT/RM/DCX object); row 15 (each II-* leg implies CII_n: II-1/II-2 via
δ_n^{pl} = 1, II-3 via CII_{n−1} ∧ T_n = e_{n−1}−1; downstream consumes ⊆
only — the S4.7 outer bound and the (P-DS) E₁-stratum clause); row 20 rows
1/2 (S2/S3's sole external = L1; the [IL3] mentions there are provenance
glosses on re-displayed in-note proofs); row 21 legs 1/3/4 (leg 1: S2's sole
[IL] object = EQ12-ADD; leg 3: REALIZE/WELL-DEF/READ-ADD externals = S0.2
textbook base facts + [IL3]† m = 1 displays, complete; leg 4: [IL]† failure
kills L6's n = 1 induction base ⟹ row 4 falls at every rung — the r4 S4.1
edge is dominated, the clause stays TRUE). All CONFIRMED.

## §5 PE5-F1 in full (the one finding)

**The offending passages (r4 sweep bracket, S7 head):** "This bracket closes
the genre by exhaustive enumeration: EVERY dependency/exemption claim in this
note (grep patterns: 'only / alone / NOT affected / self-contained / free /
independent / consume(s) / never'), each verified against the ACTUAL
consumption sites …" and "After this sweep, every dependency/exemption claim
in the note is either verified against its consumption sites or carries a
dated correction bracket — zero unverified dependency claims remain."

**The counterexample site (S0.3, the theorem statement's convention
parenthetical, lines 207–208; display tag line 201):** "(Convention at
j = 1: w₀Φ₀ := 0 and γ₁ = h₀, so S₀ = D₁h₀ + S₁ℓ₀′ — computed by the
recursion but **consumed by nothing**.)" / "[composed shift; S₀ unused]".

**Why in-scope:** (i) it is a dependency/exemption claim (object-level
non-consumption), the exact species of table row 1 (Φ_{n+1}), which is also a
definitional-apparatus site; (ii) it matches the sweep's de facto pattern —
rows 3 and 15 quote "is consumed"/"ever consumed" sites, so "consume(s)"
covers the participle. **Why unenumerated/unverified:** it is in none of the
22 rows, and no prior pass adjudicated it (grep over all five pass reports:
the only S₀ mention in the arc is a token-census line in PE2's §notation
sweep, not an adjudication).

**The claim's content is TRUE (verified this pass):** S₀ occurs nowhere in
the note outside lines 201/207–208; every downstream consumer of composed
shifts instantiates j ≥ 1 (EXP-KIT(c) kernels at j = n..1, WINDOW's S₁,
(★)-POS's j = n..1 range); the descent display's "all S_j" holds for S₀ too
(D₁, S₁ descend; h₀, ℓ₀′ constant) without consuming it. Execution referee:
the reimpl computes S[0] and no note-keyed check consumes it (its S-array
equality comparisons in descent/tie checks are referee-side strengthenings,
not note consumption sites).

**Classification: GAP.** The audit bracket reports completeness under its own
stated (grep-defined) method while the method's scope contains a site absent
from the table — the identical leak MECHANISM of rounds 2–4 (one site per
round escaping a completeness display), differing in that this leaked site's
content is true. No false dependency claim results; no grade or math impact
anywhere; the r4 substantive result ("ZERO false dependency claims") is
POSITIVELY CONFIRMED by my full independent sweep. The bridge-ledger r4 block
carries the same defect ("the genre has no remaining unverified surface").
**Cure:** sweep row #23 (site: S0.3 statement convention; claim: "S₀ …
consumed by nothing"; adjudication: S₀ nowhere else in the note, all
consumers instantiate j ≥ 1; status V) + census sentences 22 → 23 + one
clause in the bridge block.

**Adjacent sites checked and DISPOSED as non-findings:** the r38 bracket's
"conditional on (RM-2)/(RM-m) ALONE" upgrade clauses (true in the ledger's
grading semantics — the open-conditionality set at rungs ≥ 3 is exactly the
RM family, [IL]/[IL3] being ACCEPTED; surface covered by PC3/PE4's full-S7
audits); the row-18 claim's S1/S3 duplicate sites and the row-9 claim's S0.3
table-cell duplicate (same claims, true — a folding-granularity
inconsistency with the per-site rowing of the C-r4 claim, presentation
only); S2's "no window hypothesis needed except WINDOW-(n)" (true — all five
other S2 lemmas' proofs re-checked window-free; not pattern-matching); II-2's
"(WEIGHT clauses only)" micro-scope note (true — R¹/Q¹ enter II-2/II-3 only
through weight lines); S0.1's "the proof ring-blind" (scope descriptor; the
proof is stated over a general DVR).

## §6 Fresh content sweep (clean)

Standing-surface re-derivations, all exact: SHIFT-(n) (top + step, incl. the
Bézout conversion 1 − ℓγ_j = e(ℓ′ − ℓwΦ)); D_j-INT; (★)-POS (active-case
chain: e_{j−1}S_{j−1} ≥ (g_{j−1}−1)e_{j−1}γ_j + γ_j + h_j/e_j > γ_j);
WINDOW-(n) (both branches); slotwise cocycle; descent; EXP-KIT (a)/(b)/(c);
REALIZE-(m) (descent invariant γ⁽ⁱ⁾ ≥ γ_m/e_{m−1} > e_{m−2}g_{m−2}γ_{m−1};
(R1) via k_i ≤ e_{m−1}g_{m−1}−1; m = 1 admissibility u(β) > (g₀−1)h₀);
WELL-DEF-(n) ((g_m−k)γ_{m+1} ≥ γ_{m+1} > e_{m−1}g_{m−1}γ_m); READ-ADD;
L6-(n) step (telescope + single-digit + on-line grid); CASE-SPLIT (overflow
logic both E₁ᴵᴴ branches); S4.5 Case I (grid at Γ″, s_{n+1}(Γ″) = T_{n+1} −
δe_n); II-1 in full incl. the ε′-carry/canonical-lift cancellation (C₀ =
−c_{n−1}vε_{n−1}(B_{n−1}) = z_n^{δ_n^{pl}}vε_{n−1}(B_{n−1})); II-2 slot
lines; II-3 incl. the PC-G4 bracket's Q¹ bound (line − B_n = 2h_{n−1} —
re-derived exactly); the S4.4 weights display (≥ B_n + h_{n−1} at CII); the
S4.7 outer-bound proof; the S5 assembly (per-level kernels, δ_j^{pl}
cancellation). Both S7 branches re-read as amended r4: internally consistent,
correct rung scoping, the r38 bracket's good-direction upgrades consistent
with the table. The S8 section's every number matches the fresh diag run
(§3). No finding beyond §5.

## §7 Provenance appendix (verbatim slices @ 0672082)

* Note md5: `5811db126d1ed0824e4870b20e0fd774`; base (4d0eeb1 text) md5
  `c088101c9676118566a54ad3bb18dfdf` — both re-computed this pass.
* PE5-F1 site, lines 199–201 and 206–208 (S0.3 recursion display + convention):
  "`S_{j−1} := D_j·γ_j + S_j·(ℓ_{j−1}′ − ℓ_{j−1}·w_{j−1}Φ_{j−1})`
  `[composed shift; S₀ unused]`" · "(Convention at j = 1: w₀Φ₀ := 0 and
  γ₁ = h₀, so S₀ = D₁h₀ + S₁ℓ₀′ — computed by the recursion but consumed by
  nothing.)"
* Sweep closure sentence, lines 1143–1146: "After this sweep, every
  dependency/exemption claim in the note is either verified against its
  consumption sites or carries a dated correction bracket — zero unverified
  dependency claims remain.]**"
* Sweep head, lines 1101–1104: "…closes the genre by exhaustive enumeration:
  EVERY dependency/exemption claim in this note (grep patterns: "only /
  alone / NOT affected / self-contained / free / independent / consume(s) /
  never"), each verified against the ACTUAL consumption sites…"
* Row 1 (species precedent), line 1113: "| 1 | S0.1 lifts bullet | "the
  cocycle never consumes Φ_{n+1}" | anchors/val use Φ₀…Φ_n only; the lift
  construction stops at Φ_n | V |"
* Rows showing de facto "consumed" pattern coverage: line 1115 (row 3, "no
  printed formula and no text extraction is consumed"), line 1127 (row 15,
  "only the containment is ever consumed downstream").
* r4 attribution at the S4.2 close, lines 572–587 (checked against my §2
  re-derivation): "…The telescope input deg Φ_{j+1} = e_jg_j·deg Φ_j (with
  Φ_{j+1} monic, as the division algorithm at the next level requires) holds
  only given REALIZE-(m)'s (R1) degree bound deg C_k < deg Φ_m PLUS the
  existence of the C_k — WELL-DEF(i) — applied to the S0.1 lift construction
  … Corrected attribution: unconditional at every rung given [IL] + S4.1
  (rung 1 — whose tower has no canonical lift — given [IL] alone)."
* S10 DAG edge added, lines 1367–1369: "REALIZE-(m)/WELL-DEF-(n) [S4.1] →
  L6-(n)   [rungs ≥ 2]".
* Re-run artifacts: fresh diag md5 `7c72c4c6c0a953ebd41a56eab1e266e1`
  (= committed `iterlawn_diag_output.txt`); fresh reimpl md5
  `cfad79439821551f9c6a572f5d627d0b` (= committed
  `iterlawn_pe_reimpl_output.txt`); verdict lines: "== VERDICT: baseline
  violations = 0; mutations caught+visible = 7/7; elapsed 7.0s ==" / "==
  VIOLATIONS: 0 == … DIAG VERDICT: CLEAN"; diag counts sum = 5,311.
* Prior-pass S₀ record (the only one in the arc), PE2 report line 77 + 115:
  a token-census line in the notation sweep ("(S_{...}/S_j/S_n/S_m/S_r/
  S₀₁₂...) over S4.3–S4.7 (lines 562–963)", "the composed chain is S_n…S₀,
  no S_{n+1} exists") — not an adjudication of the S₀ non-consumption claim.

— ITERLAWN-PE5, campaign 2026-08-08 (wallclock 2026-08-03), on 0672082.
