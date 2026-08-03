# ITERLAWN pass PE2 — Fable round-2 hostile pass on ITERLAWN_PROOF_2026-08-08.md @ ac03cb1 (errata round 1)

**FINDINGS: 0 critical, 1 gap (+2 nits); VERDICT: NOT-CLEAN (0C/1G) — the
one gap is NEW, NARROW, and ERRATA-INTRODUCED (a false "only" clause inside
the E4/PC-G5 [IL]†-failure-branch bracket: row 2's EXP-KIT is claimed to
keep a self-contained proof with "only the rung-1 instance citation" riding
[IL], but the S3 proofs of EXP-KIT (b) and (c) both consume L1 = [IL S2 L1];
one-clause cure). EVERYTHING ELSE PASSES: errata fidelity VERIFIED
(bracket-additive, 19 dated brackets + 1 dated in-row qualifier, zero
deletions, proved-core claims unchanged, every bracket cures its finding);
E1 DEEP-CHECK CLEAN (59/59 capital-S body tokens in S4.3–S4.7 classified,
ALL raw-sum/T-renamed, 0 MISSED, 0 composed-shift occurrences in the renamed
range — the head erratum's "NEVER appear" claim verified; the four
load-bearing T-identities independently re-derived TRUE under the raw
reading, false/ill-typed under the composed one — NO EQUIVOCATION,
independently confirmed); E2/E3 corrected chains independently re-derived
RIGHT; E5 at all 3 sites; E6 pastes byte-match the ledger sources (machine
diff); both executables re-run BYTE-EXACT (md5-identical outputs); no new
battery needed (E1 renames — the referee mapping confirms no testable
semantics changed). The acceptance counter stays 0/2; the errata cost of
this round is one clause + one number.**

Verifier: Fable (ITERLAWN-PE2), fresh context, wallclock 2026-08-03
(campaign 2026-08-08). Target: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md`
at ac03cb1 (1,281 lines; errata round 1 applied per the 9f9910c remedies).
Discipline: full fresh read of the amended text FIRST; round-1 reports
(`ITERLAWN_passPE_report.md` @ e7e9151, PC findings in
`VC38_and_ITERLAWNPC_reports.md`) read only AFTER my own view was formed.
The Codex round-2 leg (PC2) is sequenced on this verdict.

---

## 1. ERRATA FIDELITY (charge 1)

`git diff e7e9151..ac03cb1 -- lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md`:
**216 insertions, 1 deletion.** The single deleted line is the S0.3 status-
table row `DCX-(n): outer bound per level | PROVED, generic`, re-emitted in
place with the dated bold qualifier `**(given IH package — errata r1,
PE-G1)**` appended — additive-within-the-line (a table cell cannot hold a
block bracket), dated, attributed; original wording preserved. All other
changes are pure insertions. No proof text of S0–S10 was touched; the
proved core's claims are unchanged (the one qualifier is an honest
DOWNGRADE demanded by PE-G1). Sealed artifacts untouched (md5s verified,
§4 below).

**Bracket census: 19 dated block brackets + the 1 in-row qualifier** (the
commit's "19 brackets" count is consistent). Cure mapping, each verified
at-site:

| # | site (line @ ac03cb1) | finding cured | verified |
|---|---|---|---|
| 1 | HEAD DECLARATION (66–110) | PC-C2 + PE-G2 (E6) | ✓ §3.4 |
| 2 | S0.3 excluded-locus bullet (218–220) | PE-G1 (E5) | ✓ |
| 3 | S0.3 table row (255, in-row) | PE-G1 (E5) | ✓ |
| 4 | S2 (★)-POS note (383–387) | PE-N2 | ✓ (count nit, §5 N1) |
| 5 | S4.1 OPERATIVE CONSUMPTION SITE (508–522) | PE-G2 substantive site (E6) | ✓ §3.4 |
| 6 | S4.3 NOTATION ERRATUM head (564–598) | PC-C1 (E1) | ✓ §2 |
| 7–15 | 9 "Notation r1" site brackets (632, 645, 654, 691, 774, 818, 848, 873, 936) | PC-C1 (E1) | ✓ §2 |
| 16 | S4.6 RM-1 exponent-chain erratum (761–772) | PC-G3 (E2) | ✓ §3.1 |
| 17 | S4.6 II-3 Q¹ bound erratum (877–890) | PC-G4 (E3) | ✓ §3.2 |
| 18 | S4.6 II-3 E₁-export supplement (892–896) | PE-N1 | ✓ §3.2 |
| 19 | S4.7 outer-bound erratum (915–924) | PE-G1 (E5) | ✓ |
| 20 | S7 [IL]†-failure branch (1139–1155) | PC-G5 (E4) | PARTIAL — finding F1, §3.3 |

E5 cross-check: the S4.7 bracket says "the same qualifier is bracketed at
the two S0.3 display sites" — exactly sites 2+3 above ✓; the S7-rows-5/6
analogy and the honest "engine-free-support lemma plausible, NOT claimed"
display are correct (my round-1-independent read of the S4.7 proof agrees:
it consumes IH (P-DS) E₁ ⟹ CII_{m−1} ⟹ g_{m−2} = 1, and (P-DS) at rungs
≥ 3 is (RM)-conditional).

---

## 2. E1 DEEP-CHECK (the critical): the T_j renaming is COMPLETE

**Method.** Machine grep of every capital-S subscripted token
(S_{...}/S_j/S_n/S_m/S_r/S₀₁₂...) over S4.3–S4.7 (lines 562–963),
partitioned body-text vs errata-bracket, then hand-classified each body
token: raw-sum (⟹ T-renamed by the head erratum or a site bracket),
composed-shift (must NOT occur here), or MISSED.

**TOKEN CLASSIFICATION TABLE (body text of S4.3–S4.7):**

| subsection | body tokens | raw-sum (T-renamed) | composed-shift | MISSED |
|---|---|---|---|---|
| S4.3 ((P-DS) L611–617; base ¶ L621–624; link ¶ L644) | 12 | 12 | 0 | 0 |
| S4.4 (L665–686) | 12 | 12 | 0 | 0 |
| S4.5 (L696–699) | 5 | 5 | 0 | 0 |
| S4.6 (II-1 L782–814: 13; II-2 L823–845: 6; II-3 L852–869: 7) | 26 | 26 | 0 | 0 |
| S4.7 (outer proof L931/933: 3; m = 2 sharp form L945: 1) | 4 | 4 | 0 | 0 |
| **TOTAL** | **59** | **59** | **0** | **0** |

Bracket-internal tokens (26 more) are all either the head erratum's meta-
display of the composed object (correctly labeled as the OTHER layer), the
declared quoted-frozen [IL3] S₁ (= T₁), or already-T text. Every body token
is covered by the head erratum's enumeration or by its subsection/leg
bracket (each bracket's token list checked verbatim against its leg — all
match; the II-1 bracket's "S_nγ_n = B_n − e_{n−1}B_{n−1}" is a trivial
rearrangement-quote of the body's "e_{n−1}B_{n−1} + S_nγ_n = B_n"). The
head erratum's structural claim — **"The composed shifts S_j NEVER appear
in S4.3–S4.7; the two layers meet only through B_j and δ_j^{pl}"** — is
TRUE on this census (0 composed occurrences; the case legs consume only
B_j, δ_j^{pl}, γ_j, ε_j, and raw sums).

**S5/S7 composed-shift retention check ✓:** S5 keeps composed S_j exactly
where it must (β_j″ = B_j + S_j via SHIFT-(n); EXP-KIT(c) with T = S_j;
D_j = (s_j-defect + ℓ_{j−1}S_j)/e_{j−1}); likewise S0.3/S2/S3-instantiation/
S6.1/S6.3 (S_n = 0, S_{n−1} = δ_n^{pl}γ_n; passthrough S_{j−1} = S_j)/S6.4/
S8 — all composed, all correct. The S7 r38 bracket's "S₁+s(γ₂) ≥ 2e₀" sits
inside the byte-frozen quoted ledger block, declared as [IL3]'s own raw-sum
notation both at the head [IL3]† parenthetical and in the S4.7 site bracket ✓.

**The four load-bearing T-identities, independently re-derived** (all TRUE
under the raw reading; under the composed reading #1/#4 are ill-typed —
the composed chain is S_n…S₀, no S_{n+1} exists — and #1–#3 false in
general):

1. **Slot-line identity** e_{n−1}B_{n−1} + T_nγ_n = B_n: sum
   β_n = e_{n−1}β_{n−1} + s_nγ_n over the pair (the S0.2 split display);
   B_n = e_{n−1}B_{n−1} + (s_n+s_n′)γ_n = e_{n−1}B_{n−1} + T_nγ_n. ∎
   (Feeds the II-1 slot-k line, the E3 bracket, and the S4.4 weights.)
2. **Range** T_n ≤ 2e_{n−1}−2 (each eq12 slot normalized 0 ≤ s ≤ e−1),
   hence in II-1 (δ_n^{pl} = 1 ⟺ T_n ≥ e_{n−1}, using δ ∈ {0,1} from the
   range): k := T_n − e_{n−1} ∈ [0, e_{n−1}−2]. ∎
3. **Grid read** s_n(B_n) = T_n − δ_n^{pl}e_{n−1}: L1 at (e_{n−1}, h_{n−1})
   applied to the pair (β_n, β_n′), with δ_n^{pl} = ⌊T_n/e_{n−1}⌋ = the
   S0.2 plain carry. ∎ (II-1: = k at δ = 1; II-3: = T_n at δ = 0.)
4. **Top grid** Γ″ = e_nB_n + T_{n+1}γ_{n+1} (sum γ = e_nβ_n + s_{n+1}γ_{n+1}
   over the pair) and s_{n+1}(Γ″) = T_{n+1} − δe_n (L1 at (e_n, h_n)). ∎

**Referee mapping (no new battery needed — confirmed).** The PE reimpl
(`iterlawn_pe_reimpl.py`, frozen at e7e9151, md5 cae45db2318b89520dd5484466ef3604)
implements the renamed objects as `ssum[j] = s_j + s_j′` in exactly the
renamed predicates (K8 P-DS support/weight/read, CII chain, K9 CASE-SPLIT,
k = ssum − e, K9b II-leg substitution identities, K10 DCX outer/sharp) and
the composed `S` only in the S0.3 constants (K1/K3/K13) — the rename maps
note-tokens to referee objects 1:1 with no predicate change; E2–E6 alter no
testable semantics either (E2/E3 are proof-internal display corrections
with unchanged conclusions; E4/E5/E6 are grade/citation displays). Both
re-runs byte-exact (§4) — semantics unchanged, as required.

---

## 3. E2/E3/E4/E6 (charges continued)

### 3.1 E2 (PC-G3): the corrected RM-1 exponent chain — RE-DERIVED RIGHT

deg f < deg Φ₁ and deg Ĉ₁ < deg Φ₁ (WELL-DEF(ii) (Ĉ1) at m = 1) give
Φ₀-developments with i ≤ e₀g₀−1, k_j ≤ e₀g₀−1, so parents
b_ic_jΦ₀^{i+k_j} sit at i+k_j ≤ **2e₀g₀−2** ✓. DIGIT-SPLIT on the
coefficient product (= lift + πX + Φ₀Y; deg Y ≤ 2(d₀−1) − d₀ < d₀ so Y is
a legal coefficient) leaves lift/πX children at i+k_j but raises the Φ₀Y
child to i+k_j+1 ≤ **2e₀g₀−1** ✓ — the original box display ("children
≤ 2e₀g₀−2") was indeed off by exactly this one child-class, as the bracket
diagnoses. 2e₀g₀−1 < 2e₀g₀ keeps EVERY child strictly inside DEV-1's
quantifier range 0 ≤ j < 2e₀g₀ ✓, so DEV-1 applies to every child and the
factored read z₁^{ε′}·v·τ₁ is unchanged; conclusion and scope of (RM-1)
unaffected ✓. The bracket's chain is exactly this — CURED.

### 3.2 E3 (PC-G4): the II-3 Q¹ line bound — RE-DERIVED RIGHT

Engine weight clause on E₁ᴵᴴĈ at level n−1: w_{n−1}(Q¹) ≥ λ + γ_n −
w_{n−1}Φ_{n−1} with λ = w_{n−1}(E₁ᴵᴴ) ≥ B_{n−1} − e_{n−2}γ_{n−1} (IH
(P-DS)) and w_{n−1}Φ_{n−1} = e_{n−2}γ_{n−1} (g_{n−2} = 1 forced by
CII_{n−1}) ✓. Q¹ at Φ_{n−1}-slot 1 of E₀ⁿᵉʷ:
line ≥ e_{n−1}(B_{n−1} − 2e_{n−2}γ_{n−1} + γ_n) + γ_n ✓. With
B_n = e_{n−1}B_{n−1} + T_nγ_n, T_n = e_{n−1}−1 (identity §2.1 + the II-3
stratum): line − B_n = e_{n−1}(γ_n − 2e_{n−2}γ_{n−1}) + γ_n − (e_{n−1}−1)γ_n
= 2γ_n − 2e_{n−1}e_{n−2}γ_{n−1} = **2h_{n−1} > 0** ✓ (γ_n =
e_{n−1}e_{n−2}γ_{n−1} + h_{n−1} at g_{n−2} = 1; h ≥ 1). Matches the
bracket display line-for-line; the "similarly" of PC-G4 is discharged; the
pre-existing R¹ bracket (line − B_n = h_{n−1}) re-checked ✓. The PE-N1
supplement also re-derived ✓: w_n(E₁ⁿᵉʷ) = e_{n−1}w_{n−1}(E₁ᴵᴴ) ≥
B_n − e_{n−1}γ_n + h_{n−1} ≥ B_n − e_{n−1}γ_n — propagates with h_{n−1}
to spare. CURED.

### 3.3 E4 (PC-G5): the [IL]†-failure branch — RIGHT on rows 1/4/5/6/8/10; ONE FALSE CLAUSE at row 2 (FINDING F1)

Verified right: structural [IL]† failure invalidates (ITER-PKG-1)
((P-L6)/(P-WM)/(P-DS) at r = 1 are [IL] displays) ⟹ L6-(n) loses its
induction base (row 4, every rung) ⟹ every value-level clause falls (rows
5/6/8 + row-10 field clauses) — NOT merely "open at the rung-2 link" ✓.
Row 1 to "open at L1" ✓ (the integer layer's sole [IL] consumption is
EQ12-ADD; D_j-INT's congruence is derived inline; row 9's integer
corollaries ride row 1's fallback under "the integer layer" — acceptable).
Row 3 ✓ (REALIZE/WELL-DEF/READ-ADD ride the S0.2 elementary base facts +
[IL3]†'s m = 1 displays; engine-free, and [IL3] is independently ACCEPTED).
Rows 7/11 already open/evidence ✓.

**F1 [GAP — errata-introduced, narrow]: the row-2 clause is false.** The
bracket asserts: "Row 2 (EXP-KIT) keeps its self-contained S3 proof (only
the rung-1 instance citation rides [IL])." But the S3 proofs consume L1
twice: EXP-KIT(b) — "substitute s(β+β′) = s(β)+s(β′)−δe **(L1)**" — and
EXP-KIT(c) — "substitute **L1** and ℓ(β″−β−β′) = ℓT"; and L1 is
[IL]-owned by the note's own S2 declaration ("Consumed; the two-line proof
is in [IL S2]"). The note's own S3 parenthetical states the correct
scoping: "self-contained **modulo the ACCEPTED [IL] alone**." Under the
bracket's hypothetical, row 2 falls back to "open at L1" EXACTLY like
row 1 (same two-line independently-re-derivable cure, already displayed
for row 1) — it does not stand whole. Failure scenario: a reader of the
S7 ledger prices a structural-[IL]-failure recovery as "row 1 only" when
rows 1 AND 2 both need the L1 re-derivation. No proved claim rides on the
branch (it is a hypothetical display; "no such failure signal exists");
cure is one clause ("row 2 joins row 1's open-at-L1 fallback; EXP-KIT(a)
and the kernel statements are L1-free"). Same genre/severity as round-1
PE-G1.

### 3.4 E6 (PC-C2 + PE-G2): head declaration — FAITHFUL

Machine comparison (whitespace-normalized): the three [IL3]† pastes (head
declaration L91–102, S4.1 operative site L508–522, S7 r38 bracket
L1081–1088) are **all byte-identical to the ledger block "[IL3] ACCEPTED —
2026-08-03"** (BRIDGE_ADJUDICATIONS:7905–7912; 541 normalized chars each,
exact match). The [IL]† scope sentence matches the "ITER-LAW ACCEPTED —
2026-08-03" block (BRIDGE_ADJUDICATIONS:6654–6656) verbatim ✓. The
convention statement matches the 9f9910c standard exactly (full paste at
declaration + operative sites — here / S4.3 base ¶ / S4.1 / S7 r38 — dagger
incorporation-by-reference everywhere else) ✓. The S4.1 operative paste is
PRESENT and correctly scoped (its "realize-constructions are
DCX-independent and engine-free; the fenced DEV-1 corner does not touch
them" claim checks: WELL-DEF(i)/(ii) are realize₁-based, no DEV-1 call) ✓.
The seven PE-G2 naked sites are enumerated verbatim ✓; the
composition-time-history paragraph resolves the frozen "0/2" body tokens
without editing them (the S0.1 entry in its site list is a method gloss
rather than a grade description — over-inclusion, harmless) ✓.

---

## 4. EXECUTION LEG (charge 2): both re-runs BYTE-EXACT

Re-run on this machine, fresh shell, exit 0 both:

    md5 iterlawn_pe_reimpl re-run output:  cfad79439821551f9c6a572f5d627d0b
    md5 iterlawn_pe_reimpl_output.txt:     cfad79439821551f9c6a572f5d627d0b   IDENTICAL
    md5 iterlawn_diag re-run output:       7c72c4c6c0a953ebd41a56eab1e266e1
    md5 iterlawn_diag_output.txt:          7c72c4c6c0a953ebd41a56eab1e266e1   IDENTICAL

Reimpl actuals confirmed at the counters: baseline violations 0 across the
22,369 family-checks on 940 pairs / 9 fresh instances (K1_shift 3,444 ·
K2_dint 940 · K3_star 3,444 · K4_window 940 · K5_l6 940 · K6_wmult 940 ·
K7_law 940 (+9 on-DCX exact) · K8_pds 3,421 + K8_e1 711 · K9_case 2,490 ·
K9b_subst 466 · K10 940/9 · K11 RM-1 308 + 16 corner / RM-2 158 / RM-3 52 ·
K12 90×3 · K13_pass 1,320 · K15 244+244 · I_m 94 · R123 38); mutations 7/7
caught+visible; "REIMPL VERDICT: CLEAN"; elapsed 7.0 s (in the frozen
output, hence byte-matched). Diag actuals: 0 violations, ~5,300 (5,311)
family-checks, 2.5 s, "DIAG VERDICT: CLEAN". **No new battery composed** —
per the charge and §2's referee mapping, no bracket changed testable
semantics (E1 renames; E2/E3 fix proof-display arithmetic with conclusions
unchanged; E4/E5/E6 are grade/citation displays).

---

## 5. FRESH CONTENT SWEEP (charge 3, under the incorporation convention)

Full fresh read of all 1,281 lines before any round-1 report. Re-verified
by hand on this pass (beyond §§2–3): the (★)-POS active-case chain
(e_{j−1}S_{j−1} ≥ (g_{j−1}−1)e_{j−1}γ_j + γ_j + h_j/e_j > γ_j) and restart
case; WINDOW-(n) incl. the S₁ > (e₀−1)h₀ worst case; the S4.4 weights
display (= B_n + h_{n−1} exactly at g_{n−2} = 1, "≥" safe); the II-1
e_n = 1 read-0 leg (B_n − γ_{n+1} = B_n − e_{n−1}γ_n − h_n <
w_n(E₁ⁿᵉʷ) = B_n − e_{n−1}γ_n at g_{n−1} = 1 — the header's
corrected-inequality claim holds); S6.3's composed collapses (S_n = 0,
D_n = δ_n^{pl}, S_{n−1} = δ_n^{pl}γ_n at e_n = 1; passthroughs); the
PE-N2 mechanism claim — re-derived as a THEOREM, not just instance-true:
equality e_jS_j = γ_{j+1} needs the top restart branch with e = 1 ∧
carry = 1 (active steps are strict by +h_j/e_j; restart gives
e_{j−1}δ_j^{pl}γ_j = γ_j only at e_{j−1} = 1 ∧ δ_j^{pl} = 1), and e = 1
grids have s ≡ 0 hence carry 0. Dagger-standard sweep: every bare
[IL]/[IL3] body token reads †-incorporated per the head declaration; the
four designated operative sites carry full pastes; the substantive [IL]
proof-consumption sites (S2 L1, S4.2 L6 base, S5 rung 1) carry
package pastes independently. No further findings.

**FINDING F1 [GAP — errata-introduced, narrow, display-grade]:** §3.3
above. The E4 bracket's row-2 clause ("Row 2 (EXP-KIT) keeps its
self-contained S3 proof (only the rung-1 instance citation rides [IL])")
is false: EXP-KIT (b)/(c)'s S3 proofs each consume L1 = [IL S2 L1], so
under the bracket's own hypothetical, row 2 falls back to "open at L1"
exactly like row 1. Contradicts the note's own S3 scoping parenthetical
("self-contained modulo the ACCEPTED [IL] alone"). One-clause cure. (The
same over-claim appears in the errata unit's ledger record, "rows 2/3 keep
self-contained/generic proofs" — cure both.)

**NIT N1 [numeric in the PE-N2 bracket]:** "equality attained 0 times in
3,444 diag + 3,444 PE-reimpl checks" — the reimpl figure is right
(K3_star = 3,444) but the diag's (★) coverage is 464 (A2_star) + 544
(B4_star) = 1,008 counter rows = 3,568 pair-level evaluations (464×3 +
544×4); no diag counter reads 3,444 (the number was evidently copied from
the reimpl). The claim's substance survives (equality is provably
unattainable, §5 above; 0 attained on all data), only the diag-side count
is wrong.

**NIT N2 [bookkeeping, outside the note]:** the ac03cb1 commit message and
the BRIDGE_ADJUDICATIONS errata record say E1 = "S4.3 head + 10 site
brackets"; the note carries the head + **9** site brackets (grep
"Notation r1" = 9), matching the record's own nine-item site enumeration
(base r=1 · link r=2 · S4.4 · S4.5 · S4.6 pre-legs · II-1 · II-2 · II-3 ·
S4.7). Off-by-one in the description only; nothing in the note is affected.

Also checked and CLEARED (no finding): the E4 bracket's silence on row 9
(covered by row 1's "the integer layer" fallback — row 9 is labeled integer
corollaries); the S4.7 notation bracket's byte-frozen-paste parenthetical
(correct on careful parse; the m = 2 sharp form's S₁ is separately declared
= T₁); the composition-time list's inclusion of S0.1 (over-inclusive,
harmless); the one in-row table edit (dated, additive-within-line, §1).

---

## 6. VERDICT MECHANICS + CONSUMABLES

Round 2, PE leg: **NOT-CLEAN 0C/1G (+2 nits)** — the clean bar (0C/0G) is
missed by F1 alone, which is errata-introduced and one clause wide. The
acceptance counter stays **0/2**. Recommended errata round 2 (cheap): (i)
F1 one-clause cure in the E4 bracket (+ mirror in the ledger record); (ii)
N1 diag count corrected to its true figure; N2 optionally noted at the
ledger. PC2 (Codex round 2) is sequenced next per the wave-20 plan; its
charge should include re-checking the E4 row-2 clause independently.

Consumables read IN FULL or at cited slices: the target note (all 1,281
lines, fresh-first); the e7e9151..ac03cb1 diff (all hunks); round-1 reports
AFTER (ITERLAWN_passPE_report.md; VC38_and_ITERLAWNPC_reports.md);
BRIDGE_ADJUDICATIONS (the two acceptance blocks at :6643/:7902, the
9f9910c adjudication + r38b + ITERLAWN-errata records); ROOT_ASSEMBLY r38b
convention bracket; both executables + frozen outputs (re-run, md5'd).

— ITERLAWN-PE2, round 2 (errata fidelity + execution + content), Fable.
