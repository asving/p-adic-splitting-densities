# GRTW2 passPE1 report — hostile pass 1 on `GRTW2_PROOF_2026-08-08.md` (the W-2 lift junction)

**Verifier:** Fable hostile pass PE1 (first pass of this note's acceptance arc), fresh
context, wallclock 2026-08-06. **Target:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md`
at commit 5463f2a (attempt grade 0/2). **Read-only context:** blueprint S3.2; ACCEPTED
LIFTCORNER (its W-2 consumption + COR 2 rescope); ACCEPTED GRTJB (§0M column (d) W2-C1
restriction); WELDMASTER (M4) face; sealed probe `GRTWELD_PROBE_2026-08-08.md`;
[ILN]† S0.1/S0.2. I fixed nothing.

## VERDICT

**0 CRITICAL ERRORS. 2 JUSTIFICATION GAPS (F1 major, F2 moderate). 5 honesty/precision
defects (F3–F7, minor).** The core mathematics survives a full independent re-derivation:
W2-L0/L1/L2/L3, (HR-REC), the conjugation/mod-wrap structure of §3.2, the (ξ,w) closed
form of §3.4 (including the exact ξ_Q-power form of the linearization error and the
top-slot consistency w·ξ^{g_m} = c), the I4B boundary story, and the §5.1 transport
algebra all check out (§A below). The machine leg reproduces bit-for-bit (§B). The
W2-OPEN-1 fence (value layer OPEN, instance-confirmed only) is honest and matches what
the runner actually executes. The two gaps are both SCOPE defects: the chain-level
transport theorem W2-C3 is graded above what its sketch derives (F1), and W2-C1a's
"every level, no shared-key hypothesis" wording is contradicted by the probe's own F2
record under the natural reading (F2).

---

## F1 — JUSTIFICATION GAP (major). W2-C3's induction exits the §3 perimeter above the first twisted junction; the grade "PROVED at attempt grade given §3–§4" overstates.

Quotes (§5.2): "*Proof sketch at attempt grade.* (ii) is clause 1 applied in the
transported chamber: R(Φ^har) = w·ψ^cur(ξy) = …" and, in the same theorem, "(iii) …
NOT byte-equality of keys (**junction unit ratios persist** and are the §3.4 characters
of the transported chamber)". Grade cap: "clause 3's chain-level statements are PROVED
at attempt grade given clauses 1–2". Claims table: "W2-C3 (i)–(iii) … PROVED at attempt
grade given §3–§4; machine 44/44/44".

The defect: clause 1 (THEOREM W2-C1) is proved "**at a shared-key junction** on the §3
perimeter", where shared-key is defined byte-for-byte (§1.3: "Φ_q^har = φ_{q+1}^cls
byte-for-byte for all q ≤ m"). In the transported chamber the induction is fine up to
and including the FIRST ξ ≠ 1 junction r₀ (the conjugation at r₀ changes no key below
r₀, so that junction is shared-key and clause 1 applies). But ABOVE r₀ the transported
print key φ_{r₀}^tw and Φ_{r₀−1}^har are byte-different (unit ratios persist —
W2-C3(iii)'s own words), so every higher junction is OFF the shared-key perimeter and
clauses 1–2 as proved do not apply there. The existence of the per-junction orbit pair
(the very thing §5.1 step 1 "records") is therefore DERIVED only up to the first twist
and MACHINE-OBSERVED above it (TW-ADM/TW-STRICT 44/44). The towers where this bites are
exactly the interesting ones (interior-twist rows T3A/T3C/T3D/I4C — the 96-RED rows the
transport exists to cure). The missing bridging lemma is nameable: either (i)
representative-independence of the Def-2.12 criterion data (v_r, R_{r−1}) in the lower
keys — a GMN fact NOT in the note's literature-consumption list — or (ii) the §3
covariance theory extended from byte-shared to type-shared-but-byte-different lower
keys (a weights/support + carry statement for the KEY objects, the chain-level shadow
of the §5.4 analysis). Neither is displayed; unlike the value layer (which got the
honest W2-OPEN-1 box), the chain level got no open-lemma display. Note also that
whether (C-coll) survives into each transported chamber is never tracked, so even the
scalar form of the recorded (ξ,w) above r₀ is unwarranted by §3 as proved.

Consequence for the weld: WELDMASTER (M4) consumes "W2-C3 (ψ-transport: strict
representative at every level of the transported chain, no weight/support splits)" at
cited grade; JB row 15 consumes "W2-C3 chamber off the byte perimeter". Both carry the
conditionality by citation, so no accepted text is falsified — but what rides through
those citations is larger than the notes' readers would price from "PROVED at attempt
grade given §3–§4". Required repair: regrade W2-C3 above the first twisted junction
(or display the bridging lemma as W2-OPEN-2-style box), and track (C-coll) through the
transport.

## F2 — JUSTIFICATION GAP (moderate) + honesty defect. W2-C1a's "at every level … no shared-key hypothesis needed" is refuted, as worded, by the probe's own F2 record.

Quote (§4.1): "**LEMMA W2-C1a.** At every level m+1 (no shared-key hypothesis needed
for the harness-side data): v_r(Φ_{m+1}^har) = e_{r−1}f_{r−1}v_r(φ_{r−1}) and the
order-(r−1) polygon of Φ_{m+1}^har is one-sided …" and §6.2: "W2-C1a | vok + one-sided
polygon of the harness lift, **every level** | PROVED". Grade cap: "clause 1 … (its two
polygon legs unconditionally)".

v_r is a GMN-chain quantity (the note's own §1.2 dictionary). On the raw (untransported)
classifier chain the sealed probe recorded **6 vok/onesided FAILURES** of exactly this
statement at junctions above an interior twist (probe F2: 6/51 RED; the note's own §5.1
mechanism paragraph restates them: "the harness lift … WEIGHT/SUPPORT splits"). So "at
every level" with unqualified v_r is false; the lemma is true (and its REALIZE-R2 proof
works) only with a chamber qualifier: v_r of the chain sharing key bytes below the
junction, or of the transported chamber (the two scopes its own machine citation names:
"probe F2 … at all 45 first-divergence/top junctions; runner TW-ADM 44/44 in the
transported chambers"). The proof body establishes the HARNESS-side polygon
(slots at exact weights on one line — correct, re-derived); the identification with
GMN v_r consumes the P-index tie, whose failure above an untransported twist is
precisely what the probe refuted. Blast radius: contained — JB's accepted consumption
already reads the pair as "W2-C1a for the window object; W2-C3 for the transported
chamber" (JB §0M (d)), i.e. the repaired reading; but THIS note's statement, grade-cap
sentence ("unconditionally") and claims-table row all need the qualifier.

## F3 — HONESTY DEFECT (minor-moderate). Three machine-coverage counts in §3.3–3.4 are inflated relative to the runner's own artifacts.

* §3.3(b): "[Machine: CK-SLOT — sim-predicted ratios equal the actual slot ratios at
  **ALL 24 shared-key junctions r ≥ 3** …]". The results JSON has **22** shared-key
  r ≥ 3 junctions (28 total, 6 SKIP); CK-SLOT's 44 samples = 16 r = 2 rows + 28 r ≥ 3
  rows of which the ratio law was checked on the 22 non-SKIP ones. No 24 anywhere.
* §3.4 remark 3: "[Machine: CK-BYTE — walk verdict ≡ actual byte compare at **all 28
  walked junctions**]". Only **22** junctions were walked (`byte_walk_nodes` present on
  22 records); the 6 above-twist SKIP junctions are counted as CK-BYTE samples but the
  walk/compare never runs on them.
* §3.4 remark 3: "reproduces the probe's full F1 verdict pattern (**which 18 junctions
  RED, which 12 GREEN**)". On this runner's own 28-junction roster the split is 18 RED /
  **10** GREEN; "12 GREEN" is the probe note's figure for its differently-counted
  30-junction table, copied without reconciliation.

None of these changes any verdict (all families are genuinely 0-violation), but a proof
note's machine brackets must match its artifacts exactly.

## F4 — honesty (minor). Sealed-runner docstring prereg says "TW-PARI … PREDICT: 24/24"; the actual family has 12 samples.

The runner checks ONE top lift (the transported classifier top) per ℤ_p row = 12; the
24 was the probe's both-legs count. The 0-violation prediction held and the note reports
"TW-PARI 12/12" correctly, but the seal's sample-count miscount is disclosed nowhere.

## F5 — precision (minor). §3.5 indexes the boundary character inconsistently with §3.4's display.

Quote: "the interior formula character **ξ₄** = χ₂^{γ₃}z₂^{−e₂A₂} = (−1)^{−13} = −1 …
off by exactly a power of the interior **ϑ₄** = −1". The displayed formula is §3.4's
ξ₃ (level-indexed: ξ_{m+1} with m = 2 — the level-3 junction, GMN r = 4); §3.5 names it
ξ₄/ϑ₄ (r-indexed). §3.2's (C-coll) and §3.4's display are level-indexed, and the actual
ξ₄ of the display (= χ₃^{γ₄}z₃^{−e₃A₃} = 1 on I4B) is a different element. The
arithmetic itself is correct (verified: ℓ₀ = 2, χ₂ = z₁⁴ = 1, A₂ = 13, z₂ = −1,
ξ = (−1)^{−13} = −1; recorded orbit at r = 5 is (−1,−1) per the JSON; formula pair
(1,1)); only the subscript collides.

## F6 — precision (minor, inside a review-owed fence). §4.3's shift computation carries a sign flip.

Quote: "Shifting ℓ_{r−2} ↦ ℓ_{r−2} + k·e_{r−2} changes Def-`t(i)` by t ↦ **t − k·u_i**".
Direct computation gives t(i) = (ℓu_i − s_i)/e ↦ t(i) **+** k·u_i (s_i is ℓ-shift
invariant). The displayed orbit identity and the "T2A: h = 1, k = 2" instance are
consistent with the text only under k ↦ −k. The section's CONCLUSION (residual ℓ-orbit
= characters ξ ∈ ⟨z_m^{h_m}⟩ with coupled w; reachability iff gcd(h_m, ord z_m) divides
the ξ-exponent) is unaffected, the section is already fenced "CONVENTION ANALYSIS,
review-owed", and nothing downstream consumes the orbit reading — recording for the
eventual review.

## F7 — precision (minor). §5.4's T3A prose slightly outruns its machine key.

Quote: "every K6/K7-failing pair is an **overflow pair** whose top-dev digits differ in
bytes (16 failing pairs ⊆ 24 byte-diff pairs …)". The machine (CK-T3E) keys only the
byte-diff containment (16 ⊆ 24, exact, reproduced) and the s₂-censuses ({0} on T3E,
{0,1} on T3A); the identification of the 24 byte-diff pairs as s₂-OVERFLOW pairs is
asserted, not machine-keyed per pair. The reverse-containment honesty sentence is
correct and correctly fenced. (The e_{j−1} = 1 ⟹ s_j ≡ 0 ⟹ channel (b) never fires
step of LEMMA W2-T3E is exact and re-derived; the two-channel exhaustiveness rests on
the battery's anchor-product shape — acceptable at attempt grade.)

---

## §A. What was independently re-derived and CONFIRMED (the positive census)

1. **W2-L0** (eq12 = T-side initial point) and its consequence V_j = harness digit
   weight: exact (expanded γ_{m+1} = e_m w_mΦ_m + h_m; integer identity checks).
2. **W2-L2**: ℓ′𝔰 − ℓu′ = (𝔰 − ℓV)/e via ℓh + ℓ′e = 1; T integral since u ≡ V (mod e);
   sum = ℓkW/e = A·k; junction instance ℓW/e = A_m exact. Runner ck_mm implements
   precisely this (with the note's u′ as its `u` and the note's u as `U`).
3. **W2-L1/TH-BASE**: digit placement, on-line weights, ε₀ = 1 read; s = 0 at the
   top junction because V = e_m g_m γ_{m+1} ≡ 0 (mod e_m).
4. **(HR-REC)**: derived from S0.2's read recursion + W2-L0 + the print child
   prescription; the per-node collapse ε(V_j)·z^{T_j} = z^{A·k_j} is W2-L2 verbatim.
5. **§3.2/§3.4, the heart**: unfolding HR-REC with IH R = Θ_{Q−1}(V)·φ(ϑ_{Q−1,…}z)
   gives Θ_Q(V) = z_{Q−1}^{A_{Q−1}s(V)}·Θ_{Q−1}(u−sW) and letter twist
   ϑ_Q = z_{Q−1}^{A_{Q−1}e_{Q−1}}·Θ_{Q−1}(γ_Q)^{−1}. Writing s = ℓV − eδ, the exact/
   linearized discrepancy is **exactly ξ_Q^δ** (I verified the note's linearization
   claim as an identity: correction = [z_{Q−1}^{−e_{Q−1}A_{Q−1}}χ_{Q−1}^{γ_Q}]^δ = ξ_Q^δ),
   and ϑ_Q = ξ_Q^{−1} as the note asserts. The χ-recursion χ_Q =
   χ_{Q−1}^{ℓ′−ℓW}·z_{Q−1}^{Aℓ} drops out of the linearization (u ↦ ℓ′V, s ↦ ℓV) —
   byte-identical to the [ILN]† S_{j−1} descent operator (ITERLAWN line 230, checked).
   The mod-wrap analysis is right: evaluation at z_{Q−1} kills reduction mod ψ_{Q−2},
   evaluation at ϑz does not — so the wrap bites exactly off (C-coll).
6. **ρ_j = c·Θ_m(V_j)·z_m^{A_m e_m j}** (harness slot read = ε_m(β_j)^{−1}ψ_{m,j} by
   REALIZE R3; β_j = V_j checked), and the closed form: c/ρ_j = w_{m+1}·ξ_{m+1}^j with
   the displayed pair; top-slot consistency w·ξ^{g_m} = z_m^{−A_m e_m g_m} = c₁^{e_mg_m}
   = c holds identically. m = 1 unconditional (Θ₁ ≡ 1, no wraps, no linearization).
7. **c₁ tie**: the print exponent −ℓ_{r−2}v_{r−1}(φ_{r−1})/e_{r−2} = −A_m through the
   P-index dictionary (indices re-walked; e_{r−2}^GMN = e_{m−1}^har etc.).
8. **W2-C1's conjugate-type verdict**: ψ^{(ξ)} monic irreducible, same (e,h,g),
   ψ^{(ξ)}(0) ≠ 0; rep of t itself iff ξ^j constant on supp ψ_m (top slot forces the
   constant = ξ^{g_m}); I4B r = 4 even-support example exact. The value-functoriality
   step of the proof implicitly uses the scalar-per-slot dictionary — supplied by
   (C-coll), and the theorem IS stated on the §3 perimeter, so no scope leak.
9. **§5.1 transport algebra**: z_old = ξ·z_new, (a_i) ↦ (a_i ξ^i) — exact; the runner's
   `rescale_letter`/conjugation implements it faithfully; later junctions never touch
   the data a lower junction's residual depends on (checked index-by-index in
   `transport_leg`), so the final-chamber scans reproduce mid-transport states.
10. **T2A reconciliation** (§2.3): A₁·k = 2·2 = 4, ratio z₁^{−4} = z₁² at ord z₁ = 3 —
    matches the probe's hand account and minimal witness.
11. **W2-OPEN-1's statement vs the code**: run_battery = check_pair (K1–K7, K13) +
    gamma_checks (K12 π-shift + ρ-monodromy) — exactly the legs the note lists; K12c/
    K15/K8–K11 are neither run nor claimed. The ClsTower reading (transported keys
    under the harness ψ-byte ledger) matches `tw_pass` exactly. Fence honest.

## §B. Machine leg (re-run this pass)

* Seals: `grt_w2_checks.py` sha256 `71f8fc90…ba52` — **bit-identical** to commit
  5463f2a; `grt_weld_probe.py` sha256 `107c92b6…4ea9` — **bit-identical** to seal
  commit 55f7416; `iterlawn_pe_reimpl.py` unchanged vs HEAD; working tree clean.
* Re-run: **exit 0**; **6,403 samples, 0 violations**; all 17 families GREEN;
  boundary junctions = 1 (I4B r = 5); teeth CAUGHT (MT-TW 2/2). Every per-family count
  identical to the committed `grt_w2_checks_output.txt` (CK-MM 4396, CK-HR1/VD1 156,
  CK-REC 55, CK-SLOT 44/16, CK-XI 22, CK-BYTE 28, TW-RATIO/ADM/STRICT 44 each,
  TW-F3/F3b 684 each, TW-PARI 12, TW-QO 7, CK-T3E 2, MT-TW 2). Elapsed 3.1 s.
* JSON cross-checks used for F3/F5: shared r ≥ 3 = 22; walked = 22; SKIP = 6;
  byte-equal r ≥ 3 = 10; I4B ledger [(3,(1,1)), (4,(1,1)), (5,(−1,−1))]; T3A
  digit-diff = 24 ⊇ K6/K7-fail = 16; T3E s₂ = {0}.

## §C. Special-attention answers (the charge's six items)

1. **Closed form re-derivation**: complete, CONFIRMED (§A.5–6). The one derivation-level
   caveat is already the note's own W2-BOX-1 (wraps off (C-coll)) — honestly boxed.
2. **ψ-transport — proved or measured?** Chain level: proved up to the first twisted
   junction, MEASURED above it (F1 — the grade overstates). Value layer: measured, and
   the note SAYS so (W2-OPEN-1, honest). The 96→0 headline is correctly confined to
   machine brackets and the open-lemma display.
3. **W2-OPEN-1**: statement faithful to what ran (§A.11). Riders verified: LIFTCORNER's
   ACCEPTED r1 box (COR 2 identification WITHDRAWN, (a)/(b) owed) correctly quotes it;
   WELDMASTER carries it "OPEN — inherited displayed"; JB displays it "not claimed".
   No consumer treats it as proved.
4. **Admissible-representative clause vs JB's W2-C1 restriction**: JB §0M (d) consumes
   the pair "W2-C1a for the window object; W2-C3 for the transported chamber" with
   "W-2 clause 1's own conditionality rides" — i.e. JB already reads the REPAIRED scope
   of F2 and carries F1's conditionality by citation. No falsification of the accepted
   JB text; both findings enlarge what rides its (d) column.
5. **Evidence classes per family** (JB's IND/SAME/NONE vocabulary, which this note
   predates and does not use): CK-MM/HR1/VD1/REC/SLOT/XI/BYTE — IND (cross-engine or
   formula-vs-fresh-evaluator; sealed GmnLeg + PARI anchors). TW-F3 — IND with the best
   possible teeth (the probe's 96 REDs prove reachability). TW-PARI — IND (external).
   **TW-STRICT is construction-forced given TW-ADM** (the conjugation makes strictness
   an identity once the orbit pair exists; verified the final-chamber scan reproduces
   the mid-transport state) — as evidence it is SAME-adjacent, and §5.2's bracket
   presents it as an independent 44/44 confirmation of (ii). Fold into F1's repair.
   MT-TW teeth are real (garble caught on both designated rows).
6. **K12 legs**: in THIS note they are inside W2-OPEN-1's battery and genuinely ran —
   gamma_checks (K12 π-shift + ρ-monodromy) executes per γ per transported tower inside
   TW-F3, 0 violations (probe baseline: K12 was 0 even on the broken rows). K12c
   (constants-descent) does NOT run in run_battery and is not claimed. LIFTCORNER's
   owed item (b) (K12 under the base-junction restriction) is an obligation of THAT
   note's COR 2 tie, not a defect here.

## Repair queue implied (for the composer; I fix nothing)

R1 (F1): regrade W2-C3 above the first twisted junction OR display the missing bridging
lemma (rep-independence of the criterion data / off-byte-perimeter covariance) as an
honest box; track (C-coll) through the transport; demote TW-STRICT's evidentiary
billing. R2 (F2): add the chamber qualifier to W2-C1a (statement, grade cap
"unconditionally", claims table). R3 (F3): correct 24→22, "28 walked"→22 walked (+6
recorded SKIP), 12→10 GREEN (or reconcile with the probe's 30-junction count). R4–R7:
one-line fixes per F4–F7.

— PE1, GRTW2 acceptance arc, 2026-08-06.
