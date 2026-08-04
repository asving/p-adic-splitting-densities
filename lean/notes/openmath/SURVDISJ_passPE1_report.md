# SURVDISJ-PE1 — hostile content verification pass 1 (fresh context)

Object: `lean/notes/openmath/SURVDISJ_PROOF_2026-08-08.md` at **4f7c3ff**
(confirmed via `git log -1 --format=%h -- <file>`).  Charge: the
orchestrator's 8-point quote-and-classify charge (SD-L2 ledger; SD-L1
deficit; SD-L3/kill; SD-THM-A pins; SD-L5/L6/L7; the boxes; machine;
fresh eyes).  I verify; I fix nothing.  Date: 2026-08-08 campaign
(wallclock 2026-08-04).

Sources read in full or at the cited displays: SURVDISJ_PROOF (whole),
SURVDISJ_INSTRUMENT (whole), WMULTDCX_2026-08-08.md (whole; W-D1/2/3/4/5/7),
SURV_PROOF_2026-08-08.md (whole; S-L0/1/3/4, S-THM, S7 box, F-C, S-r1
record), RMENGINE_2026-08-08.md (L-NORM display S2.1, S2.2 child
inventory, L-LINE), EMPTY_PROOF_2026-08-08.md (E-L6 + the W-D1 leg,
header grades), both runners (`survdisj_derive_checks.py`,
`survdisj_instrument.py`) line-by-line, both committed artifact sets.

## §1. Charge 1 — SD-L2 (the E-weighted mass ledger) and (★): RE-DERIVED, VALID

**SD-L2, from LED_l (W-D3), independently.**  LED_l says
j_l(node) = σ_{l+1} + j_l(D) + π_l + dmp_l − cons_l.  Multiply by E_l,
sum l = 0..m−1, and expand each aggregate term against the [RMG] S2.2
child inventory (verified verbatim at RMENGINE S2.2, quoted below in §3):

* Σ E_l·σ_{l+1} = M(σ⃗)  (X₀ seeds j_{l} = σ_{l+1}, W-D1) — note M(σ⃗)
  here means Σ_{l=1}^{m} σ_l E_{l−1}, the σ-vector placed at levels
  0..m−1; index-consistent with the (★) usage.
* Σ E_l·j_l(D) = M(j⃗(D))  (stage-2 seeding).
* Σ E_l·π_l = Σ_{l=1}^{m−1} π_l E_l  (π₀ = 0).
* Σ E_l·dmp_l = Σ_{c∈CE} (Σ_{l<i_c} a_{c,l}E_l + Y_c) + Y₂  — the +1 at
  level 0 rides the Y-child of a correction (Y_c) or of the seeding
  (Y₂); E₀ = 1.  The S2.2 inventory puts the correction Y-child at
  exponents j_l + a_{d,l} with +1 at l = 0, and the i = 0 correction
  children carry no dump vector (the L-NORM split of
  b·lift(ψ₀,k)·π^{(g₀−k)h₀} at j₀ − P₀ + e₀k) — consistent.
* Σ E_l·cons_l = Σ_{l=1}^{m−1} π_l P_{l−1}E_{l−1}  (promotion out of
  l−1 = promotion into l)  + 2P_{m−1}E_{m−1}  (two exits)
  + Σ_c (P_{i_c} − e_{i_c}k_c)E_{i_c}  (corrections).
* π-junk (X) children move NO exponents (L-LINE(iii): same exponents)
  — in particular a correction taken via its X-child has the SAME
  exponent moves as via its L-child, so the Y_c ∈ {0,1} flag with the
  same defc formula covers all three correction children.  Verified
  against the S2.1/S2.2 displays.

Collecting gives EXACTLY the displayed ledger with
defc_c := (P_{i_c} − e_{i_c}k_c)E_{i_c} − Σ_{l<i_c} a_{c,l}E_l − Y_c.
The "telescope" is bookkeeping (regrouping), exact.  Every child type
of the S2.2 inventory is accounted; no edge type is missing (R-leaf
termination does not occur on a two-exit path; the terminal is the
second exit cofactor).  **VALID.**

**The pool-telescope identity, term by term.**  At (H2)∧(H3)∧g₀=1 all
P_l = e_l (l ≤ m−1), so P_{l−1}E_{l−1} = E_l and the promotion-loss sum
vanishes; 2P_{m−1}E_{m−1} = 2E_m.  With ρ_l = σ_l + s_l(u_l) + c_{l−1}
− e_{l−1}c_l (c₀ = 0):

    M(ĵ) = Σ_{l=1}^{m−1} ρ_l E_{l−1} + (c_{m−1}−k)E_{m−1}
         = Σ_{l=1}^{m−1}(σ_l+s_l(u_l))E_{l−1}
           + Σ_{l=1}^{m−1}(c_{l−1}E_{l−1} − c_l E_l)     [e_{l−1}E_{l−1}=E_l]
           + (c_{m−1}−k)E_{m−1}
         = Σ_{l=1}^{m−1}(σ_l+s_l(u_l))E_{l−1} − c_{m−1}E_{m−1}
           + (c_{m−1}−k)E_{m−1}                          [carry telescope ✓]
         = Σ_{l=1}^{m}(σ_l+s_l(u_l))E_{l−1} − D·E_{m−1} − k·E_{m−1}
         = M(σ⃗) + M(j⃗_prin) − 2E_m                      [D+k = 2e_{m−1};
                                                          e_{m−1}E_{m−1}=E_m ✓]

Each bracketed step re-checked independently; all exact.  **(★)** then
falls out of SD-L2 applied to any two-exit terminal C with j⃗(C) = ĵ,
using j⃗(D) = j⃗_prin for EVERY path (W-D2(i)–(iii) forces every
d-cell's exponent vector at (H3)∧g₀=1, any d₀; L-CELL(i) keys cells by
exponent vector, so the d-cell is unique — the S-L1 display, cited
correctly): Σ_c defc_c = Y₂(C) ∈ {0,1}.  **VALID.**  Numerical
cross-check on a real row: on W3DEEPF[663,667] the cascade slot
(0,1,0) has M = E₁ = 3 and the two killed bottom cells at slot (0,0,0)
have M = 0 with exactly one i = 0, k = 0 correction each of
defc = e₀ = 3 — the ledger's predicted mass difference M(ĵ) − M = Σdefc
= 3, EXACT (§7c).

## §2. Charge 2 — SD-L1 (strict dump deficit at g₀ = 1): RE-DERIVED, VALID

At (H2)∧(H3)∧g₀=1: g_l = 1 for all 0 ≤ l ≤ m−1, so P_l = e_l and the
only correction index is k = 0 (k < g_i = 1) — both displayed.  Then
consumption is (P_i − 0)E_i = e_iE_i = E_{i+1} exactly, and the dump
bound a_{d,l} ≤ P_l − 1 = e_l − 1 ([RMG] S2.2, quoted verbatim in the
note: "a_{d,l} ≤ P_l − 1 for l < i, a_{d,l} = 0 for l ≥ i" — faithful)
gives Σ_{l<i} a_{c,l}E_l ≤ Σ_{l<i}(e_l−1)E_l = E_i − 1 (mixed-radix
telescope, re-checked; at i = 0 the empty sum is 0 = E₀ − 1,
consistent, and the i = 0 children indeed carry no dump vector).
Hence defc ≥ E_{i+1} − E_i + 1 − Y_c, and since E_{i+1} ≥ E_i and
Y_c ≤ 1, also defc ≥ 0.  Equality analysis: defc = 0 forces Y_c = 1,
E_{i+1} = E_i (i.e. e_i = 1), and termwise-full dump a_{c,l} = P_l − 1
for every l < i.  All three legs re-derived; **VALID and complete.**

**Where g₀ = 1 enters, exactly:** (a) P₀ = e₀ (at g₀ ≥ 2 the level-0
dump window is P₀ − 1 = e₀g₀ − 1, raising the budget to
E_i − 1 + e₀(g₀−1) — I re-computed the box's budget arithmetic:
(e₀g₀−1)·1 + Σ_{1≤l<i}(e_l−1)E_l = E_i − 1 + e₀(g₀−1) ✓); (b) k = 0
(at g₀ ≥ 2 level-0 corrections with k ≥ 1 consume as little as
(P₀−e₀k)E₀ = e₀(g₀−k) — as little as e₀ at k = g₀−1 ✓); (c) promotions
out of level 0 become lossy (P₀E₀ − E₁ = e₀(g₀−1) per edge ✓); (d)
non-principal seeds inject t·e₀ at level 0 (W-D2(iv)).  So the bound
genuinely FAILS as an argument at g₀ ≥ 2 — exactly consistent with the
(SURV-K2) box's "recycle economy" display and with WMULTDCX fence F2.
The box's arithmetic is right and is honestly flagged as
budget-arithmetic-only (CTRL-DEFNEG silent, disclosed at S7(i) and
F-C).

**Sharpness:** the displayed machine minima (1, 2, 3, 4 at
e_i = 1, 2, 3, 4, all Y_c = 0) reproduce in my re-run (DEFC_MIN
g1|e=1..4|Y=0 = 1,2,3,4), and match the bound's value at E_i = 1
(bound = e_i, attained at i = 0 where defc = e₀ identically).
Consistent.

## §3. Charge 3 — SD-L3 (the kill) and SD-L4 (the E-L6 leg): FAITHFUL; one scope gap at SD-L4

**SD-L3 vs the accepted [RMG] text.**  L-NORM(c) verbatim (RMENGINE
S2.1): "the Φ₀Y-junk child π^w·Ŷ at exponent j₀ + 1 has w₀ ≥ w (absent
identically at d₀ = 1: there deg(b̂ĉ) ≤ 2d₀ − 2 = 0 < d₀, no
Φ₀-overflow, Ŷ = 0)".  The note's SD-L3 is this display applied to
every L-NORM invocation in T² (correction products b·c_d, i = 0
correction products, seedings b_Y·c_D — all with both factors of
degree < d₀, so at d₀ = 1 the primitive product has degree
≤ 2d₀−2 = 0 < d₀ in every case).  Consumption is faithful, labeled
"consumed, not composed", and IDENTICAL in mechanism to the accepted
source; Y₂ ≡ 0 ∧ Y_c ≡ 0 at d₀ = 1 on every path follows.  **VALID.**
Machine teeth honest (CTRL-Y fired 60 on the two d₀ = 2 towers).

**SD-L4 / the step-5 E-L6 leg.**  The chain "correction-free stage-1
prefix ⟹ b unchanged along promotions/exits ([RMG] S2.2) ⟹ stage-1
exit coefficient b₀ = π^{u₁+u₁′} (W-D1 identity seeding) ⟹ E-L6: the
Φ₀Y-child of the split of b₀·c is IDENTICALLY zero at ANY d₀ (deg
b̂₀ = 0 ⟹ deg(b̂₀ĉ) = deg ĉ < d₀)" is EMPTY_PROOF S6 verbatim
(E-L6 + its "why b stays monomial" leg), consumed faithfully and
LOAD-BEARING as declared.  The X-mate legs: L-NORM(b) gives the
π-junk child w₀ ≥ w + 1 at the SAME exponents (L-LINE(iii)), and after
the seeding a correction-free walk is exponent-driven and
deterministic, so the X-branch terminal (at most one) lands at the
same slot with w₀ ≥ ŵ + 1 and junk ≥ 1.  **VALID at the principal
seed.**

**FINDING G-1 (GAP — quantifier/pin display).**  Quote (S3, Lemma
SD-L4): "(ii) L-child never absent, with w₀ exactly ŵ and residue
b̄₀c̄_D ≠ 0 … (iii) π-junk X-child, IF nonzero, with w₀ ≥ ŵ + 1".
And the S9 claims row: "SD-L4 | b₀-seeding: Y-child zero any d₀;
X-mate has same slot, w₀ ≥ ŵ+1 | PROVED (attempt)" — NO pin displayed.
The (ii)/(iii) clauses hold only when the seeding d-cell is THE
principal cell (w₀(c_D) = u₀): at g₀ ≥ 2 a t ≥ 1 d-cell has
w₀(b_D) = u₀ − t·h₀ (W-D2(iv)), so its L-child has w₀ = ŵ − t·h₀ ≠ ŵ
and the X-child bound ŵ + 1 is likewise wrong.  Clause (i) IS any-d₀
any-g₀ correct (E-L6 needs only deg b̂₀ = 0), and the DRV-SEEDY
bracket ("every d-cell on every live row", incl. g₀ = 2 t-cells)
checks exactly (i) — blurring the quantifier for (ii)/(iii).  F-A
lists per-lemma pins for SD-THM-A and SD-L5/L6/L7 but is silent on
SD-L4.  DOWNSTREAM: no damage — the only consumers are SD-THM-A
(locus g₀ = 1 ∧ d₀ = 1, where the d-cell is the unique principal
cell) and SD-L5 (which uses only the fork-counting, not the ŵ
clauses); I verified both consumption sites.  Classification: **GAP**
(the statement needs a "c_D = the principal d-cell" or "(H3) ∧ g₀ = 1
for (ii)/(iii)" pin; the mathematics consumed downstream is sound).

## §4. Charge 4 — SD-THM-A clauses (i)–(v): RE-DERIVED, VALID; pins exact; no illegal S-L4(iii) consumption

Pins: the theorem head displays TRACK, (H1)–(H3), g₀ = 1, d₀ = 1,
(STK), c_{m−1} ≥ k, with (RW) added for (v) only — and F-A repeats
this.  Exact.

**(i).**  Chain re-derived: (★) gives Σ defc = Y₂(C) for any two-exit
terminal at ĵ; SD-L3 (d₀ = 1) kills Y₂ and every Y_c; SD-L1 with
Y_c = 0 makes every defc ≥ 1; hence CE(C) = ∅.  Correction-free ⟹ no
stage-1 L-NORM event ⟹ seeding is b₀·c_D with the unique principal
d-cell; its Y-child does not exist (SD-L4(i)); off the seeding no
forks (promotion/exit children unique per firing, E1-priority
deterministic — [RMG] S2.2; this IS the S-L4(iii) UNIQUENESS half,
which is the UNrescoped half).  So C is Ĉ (L-branch) or the at-most-one
X-mate (X-branch, same exponents, junk ≥ 1, ce = ∅, w₀ ≥ ŵ+1).  I
checked the subtle points: (a) CE(C) counts corrections taken via ANY
of the three L-NORM children (the X-flavored correction has identical
exponent moves and Y_c = 0), so "CE = ∅" genuinely excludes all
correction riding; (b) the X-branch also satisfies (★), consistently;
(c) a companion from a dump-fed stage-1 exit would carry CE ≠ ∅ —
excluded.  VALID.

**(ii).**  X-mate line = β̂ + E_m(w₀−ŵ) > β̂ by S-L4(i) affinity ✓.  So
the β̂-population at ĵ is {Ĉ} — (NEP) as a theorem, scope EXACTLY the
pinned locus (the S8 (NEP) bullet says "on the SD-THM-A locus" —
exact).

**(iii).**  B_ĵ = b_Ĉ + b_X with w₀(b_X) > ŵ; S-L0(b) at w₀ gives
B_ĵ ≠ 0, w₀ = ŵ, line β̂.  (Both Ĉ and mate have sign + — corrections
zero on both — so the note's "±" is conservative; harmless.)  VALID.

**(iv).**  Trivial from (iii).  VALID.

**(v).**  S-THM(c) consumed with (NEP) now supplied by (ii); its other
hypotheses ((H3)∧g₀=1∧(STK), (RW), c ≥ k) are all in the theorem head.
**The rescope question (charged explicitly):** S-THM(c) routes through
(NEP) + S-L4(ii) + S-L4(iii)'s uniqueness half ONLY — verified twice
in SURV_PROOF (PE1 + the S-r1 repair record) and re-confirmed by me at
the S6 proof text of SURV_PROOF; SD-THM-A itself cites S-L4(iii) only
for the uniqueness half (proof of (i)).  **The m = 2-forced
junk-free-forcing half of S-L4(iii) is consumed NOWHERE in this note
at any m** — the ledger route replaces it.  Clean.

Scope remarks (a)–(d) checked: (a) matches SURV_PROOF F-C + the
instrument disclosure (d₀ = 2 only at g₀ = 2 in every roster); (b)
(STK) enters via W-D7(ii) existence, kept explicit; (c) consistent
with the six K1 rows (§7c); (d) m = 1 out of scope.

## §5. Charge 5 — SD-L5/L6/L7: RE-DERIVED, ALL VALID

**SD-L5.**  Seed inventory W-D2(iv) (under (H3)): j₀(D_t) = s₁(u₁) +
t·e₀, 0 ≤ t < g₀, higher exponents principal.  A correction-free
junk-free path has no forks given its seed (same determinism argument
as THM-A(i); junk-free directly excludes X/Y children so no SD-L4
consumption needed) ⟹ ≤ 1 terminal per seed.  Distinct slots: LED_0
with no corrections/dumps/Y gives j₀(term) = σ₁ + s₁(u₁) + te₀ −
P₀π₁; equal slots ⟹ equal j₀ ⟹ (t−t′)e₀ = e₀g₀(π₁−π₁′) ⟹ t ≡ t′
(mod g₀) ⟹ t = t′ (both in [0,g₀)) ⟹ same seed ⟹ same path.  The
**t ≡ t′ mod g₀ forcing re-derived exactly**; the θ₀ = 0 remark is
right (the argument needs only distinctness of t·e₀ mod e₀g₀, not the
principal cell's presence).  VALID.  Corollary reading (kills never
consume two correction-free junk-free paths) follows with S-L3.
Instance echo: in my hand-derived K2 row (§7c) the killed pair is
exactly one correction-free cell + one correction-rider — as SD-L5
demands.

**SD-L6.**  Same slot + line ⟹ same w₀ (S-L4(i)); b_C = π^w b̂_C,
res b̂_C = res(b̄_C) nonzero (primitive part, deg < d₀ = deg ψ̄₀ so no
quotient collapse — checked); reduction mod π additive ⟹
res(Σ±b̂_C) = Σ±res(b̄_C).  Nonzero ⟹ w₀(B_G) = w exactly and
line = E_m·w + Σj_lΓ_l = β (survives); zero ⟹ B_G = 0 or w₀ ≥ w+1 ⟹
line ≥ β + E_m (dies at β).  The biconditional is exact.  **survival
iff signed residue sum ≠ 0: re-derived.**  VALID.

**SD-L7.**  Protected case (a): Σ = ±r_i with r_i ≠ 0 in the field K₀
— nonzero.  Case (b): Σ = r_a − r_b with r_a ≠ r_b DISTINCT — nonzero
by distinctness alone, characteristic-free.  Conclude by SD-L6.
VALID.  **The warning display is honest and correct:** (+1,+1) gives
r_a + r_b, and r_b = −r_a is a genuinely distinct class whenever
char ≠ 2 and r_a ≠ 0 — so (+1,+1) is rightly NOT protected; the
instrument's observed two-class survivors were exclusively (−1,+1)
(re-derived from the artifacts, §7b).

## §6. Charge 6 — the boxes, the grade cap, the consequence display

**(SURV-K2)** precisely states the existence half: some BOTTOM-LINE
group carries a protected vector; the reduction half (protected ⟹
survives ⟹ with S-L3 + (RW₀) the bottom leg + S-THM(b): Q¹ ≠ 0) is
correctly wired to SD-L6/SD-L7/S-L3.  The sign-reversing-pairing
target is displayed as a TARGET, and the constraint census is quoted
as the INSTRUMENT's (F-G says so): I re-derived every constraint from
the committed artifacts — survivor vector census **{(+1)×85, (−1)×115,
(−1,0)×5, (0,+1)×4, (−1,+1)×2}** EXACT (recomputed from survdec, §7b);
M-B1 = 39 odd killed groups EXACT; P-C fails 103/200 EXACT; CROSS
kills 9, ALL off-bottom, shapes as displayed (8 × p=3 junk-free n=3
signed (∓2,±1) with 2·res_a = res_b in F₃; 1 × char-2 mixed-junk
SDG2AF[2321,2321] junks {1,2} n=5, signed (−3,+1,−1), i.e.
res_a + res_b = res_c in char 2) EXACT.  The g₀ ≥ 2 deficit-headroom
display is budget arithmetic and disclosed as such (S7(i), F-C) —
CTRL-DEFNEG silent in my re-run too.

**(SD-YJ)** — the deficit equation re-derived (§1–§2): a companion
≠ Ĉ/X-mate at g₀ = 1 solves Σ defc = Y₂ ∈ {0,1} with all defc ∈ {0,1};
Y₂ = 0 ⟹ every correction defc = 0 (e_i = 1 ∧ Y-child ∧ full dump);
Y₂ = 1 ⟹ exactly one defc = 1 (the displayed examples check:
e_i = 1 full-dump L/X-child gives 1; i = 0, e₀ = 2, Y-child gives
E₁ − 1 = 1) — and both shapes need a real Φ₀-overflow, impossible at
d₀ = 1.  The machine-dark disclosure is accurate (no g₀ = 1 ∧ d₀ ≥ 2
tower in WS.ROSTER/ED.FRESH_ROSTER/PX/SD — checked the rosters
directly; SURV_PROOF F-C concurs).  **Nothing PROVED consumes either
box** — checked every consumption edge in the claims table and the
theorem proofs; the boxes appear only as OPEN rows and in S5/S6/S8
commentary.

**Grade cap + consequences.**  The header cap sentence and the S9
dependency line are accurate against the sources at their own heads:
WMULTDCX 0/2 CLEAN (its W-r3 record: PE1 NOT-CLEAN repaired, PE2/PE3
GAPS-ONLY); SURV_PROOF 0 CLEAN (round 1 GAPS-ONLY, repaired at S-r1,
consumed at 51a8ac9 as declared); RMENGINE accepted (round-7
double-clean per its ledger).  EMPTY at "1/2 CLEAN": the EMPTY note's
own header still says 0/1 CLEAN, but commit 7314525 records PE2 CLEAN
→ counter 1/2 — the SURVDISJ claim is CORRECT against the repo
record; the stale header is EMPTY_PROOF's hygiene issue, not this
note's (recorded as N-4 below).  The S8 display: SD-THM-A(v) + E-THM†
(scope (H1)–(H3) g₀-free — the pinned class is inside it) + W-D4†
give the law on the pinned class at capped attempt grade, m ≥ 2
uniform; class-wide stays conjecture; the 10-item "what must still
close" list is complete as far as I can tell (W arc, EMPTY arc, SURV
arc, own arc, (H2) rider, (RW) at m ≥ 3, (STK) pin, the two boxes,
(EMPTY-gen)/interior g, (H1) rider).  No overclaim found in S8/S9;
F-D/F-F/F-G honest.

## §7. Charge 7 — the machine legs

**(a) Pins and read-only re-runs.**  All committed md5s match the
note's pins: `survdisj_derive_checks.py` 3eaf69c08f9a5b278826102610d4aa22,
output be088ed43e57569cbc508082dc2d15b8, results
868f71903d53955418435c2377026723; `survdisj_instrument.py`
3df33c7406913510ed7ebaa60d480b57.  The two-commit seal is GENUINE:
61e9e36 (runner + design note with PRED-1..7, results PENDING) touches
only those two files; 00e19b4 (verdict) adds output/results and the
note's results section, runner byte-untouched.  Both runners re-run
read-only to /tmp (this pass): **outputs and results JSONs IDENTICAL
to the committed artifacts mod elapsed/timings** (json non-elapsed
diff = []; stdout diff empty after stripping timing fields).
Composer: 10 families, 0 violations; instrument: 9 families, 0
violations; 979 live rows in both, phase split 286 sealed + 330 EQ +
212 PX + 151 SD re-counted from the output lines — EXACT.  Both
runners' union-roster selection loops compared side by side: identical
logic (and empirically identical row sets).  The composer's PINS dict
= the instrument's 7 pins + the instrument runner (the note's "8 md5
pins" claim exact).

**(b) Note-vs-artifact numbers, all re-counted from my re-run:**
mass_ok 3,606 (DRV-MASS); defc_ok_g1 2,167 (DRV-DEF; DEFC_MIN
g1 = 1,2,3,4 at e = 1,2,3,4 all Y=0); y0_ok 3,274 + CTRL-Y 60
(DRV-Y0); seedx_zero 1,355 / seedx_nonzero absent (DRV-SEEDY; zero
X-mates ever); neps_ok 693 (DRV-NEPS); rig_rows 979 + CTRL-RIGSEEDS
123 (DRV-RIG); crit_ok 280 + CTRL-KILL 352 = 632 groups (DRV-CRIT);
m1_protected 56 + CTRL-M1 576 (DRV-M1); CTRL-XSEED 388; CTRL-DEFNEG
SILENT (disclosed); group census g1: 6/12 bottom kill/surv +
140/160 off; g2+: 97/31 + 109/77 — ALL matching the note's S2/S7
displays digit for digit.  Instrument headlines re-derived from the
committed json: P-A 693/693 ok (= all 693 g₀=1 live rows: 979 − 286
g₀≥2 = 693, so the stk-conditioning excludes nothing — and the
instrument's unconditional SDI-SURV cascade-count check backstops
casc-missing rows, 0 violations); PB-mult1-some 286/286; CANC = 6
total-bottom-dead rows, surv_is_casc on ALL 6; survdec = 200 kill
rows; SDI-RESFACT 3,218; P-M1 survivor-vector census recomputed
cell-by-cell from survdec: {(+1)×85, (−1)×115, (−1,0)×5, (0,+1)×4,
(−1,+1)×2} EXACT; bottom-kill genre census SIGN-PAIR 97 (66 p3 + 30
rc2 + 1 p5) + MODP 6 — EXACT.

**(c) Three instrument rows re-derived BY HAND (one per regime + one
dual-kill):**

* **K1 regime — W3DEEPF[663,667] (Fpt p=2, g₀=1, k=1=c₂).**  Bottom
  slot (0,0,0) at β_min = 456: TWO cells, each riding exactly one
  i=0,k=0 correction — sign (−1)¹ = −1 both; factorizations
  b0[w0=24]·cd(i=0,k=0)[w0=2,res=1]·cD(jD=[2,0,1])[w0=12,res=1] ⟹
  w₀ = 38 ✓ both, residues 1·1·1 = 1 equal ✓.  Net = −2·(unit) ≡ 0 in
  char 2: MODP kill, genre and mechanism confirmed by hand (matches
  SURV_PROOF's closest-call display for the same key).  Survivor: the
  cascade slot (0,1,0) at 458 = β̂, single cell, sum-free — SD-THM-A's
  prediction realized.  LEDGER cross-check: M((0,0,0)) = 0,
  M(ĵ=(0,1,0)) = 3, and each killed cell's Σ defc = (P₀)E₀ = 3 —
  M(ĵ) − M = Σ defc EXACTLY as SD-L2 predicts (the killed cells sit 3
  units of E-mass below the cascade slot, paid by their correction).
* **K2 regime — W3G2P5[459,459] (Zp p=5, g₀=2).**  Bottom-line slot
  (2,0,0) at 312: cell A = b0·cd(i=0,k=1)[res 4]·cD(jD=[2,0,1])[res 4],
  sign −, res 4·4 = 16 ≡ 1 (mod 5) ✓ hand-checked; cell B =
  b0·cD(jD=[0,0,1]), correction-free, sign +, res 1; equal w₀ = 38 ✓.
  Net = +1·r − 1·r = 0: SIGN-PAIR, characteristic-BLIND (this is the
  p = 5 witness of char-blindness).  Exactly ONE of the two cells is
  correction-free — SD-L5's corollary verified on the instance; the
  pair realizes the box's "correction ↔ t-seed shift" toggle (t=1 seed
  + k=1 correction vs t=0 seed).  Bottom survived elsewhere ((0,0,0)
  at 312) ✓.
* **Dual-kill row — SDG2BF[1479,1479] (Fpt p=2, g₀=2).**  THREE kills
  on one row: MODP off-bottom at (4,0,1) (two − cells, equal res,
  −2 ≡ 0 mod 2); SIGN-PAIR AT BOTTOM at (1,1,0) line 999 (ncorr 2 vs
  3 ⟹ signs +/− ✓ the (−1)^{ncorr} law, equal res, net 0 — char-blind
  at residue char 2, the regime cross); SIGN-PAIR off-bottom n=4 at
  (5,0,0) (two +2-corr, two −3-corr, equal res).  Survivor at
  β_min = 999: slot (4,1,0), NOT sum-free (one of the 20 netted-sum
  survivors saved by the protected-vector law), bottom AND cascade
  survive — the regimes stack with no (SURV-DISJ) counterexample,
  exactly as PRED-2 recorded.

All three hand-derivations agree with the artifacts and with the
note's displayed mechanisms; the L-NORM(a) sign/residue/valuation
chain checked by hand at every cited cell.

## §8. Charge 8 — fresh eyes: remaining findings (notes)

**N-1 (NOTE — a definitionally-forced "constraint" presented as
empirical).**  Quote (S6 box, constraint list): "the exceptionless
complementarity (no non-CROSS killed group EVER carries a ±1 class —
0 instances in 979 rows)".  Under the instrument's OWN genre taxonomy
this is a tautology, not a datum: a killed group with a ±1 class has
a signed count ≢ 0 (mod p) for every p, hence is classified CROSS by
construction (genre CROSS := not all-zero and not all ≡ 0 mod p).
The 0-instance count is therefore guaranteed by the classifier, and a
candidate pairing mechanism reproduces it for free.  The REAL
empirical content nearby is correctly displayed separately (CROSS
never at a bottom or survivor line, 979/979; the CROSS kills that do
exist carry ±1 classes off-bottom).  Affects only the box's
constraint framing (inherited from the instrument note's P-M1
paragraph); no proof step consumes it.

**N-2 (NOTE — TRACK elided in two consequence displays).**  The S8
LAW-DCX bullet and the S8 (SURV-DISJ) bullet display the pinned class
as "(H1)–(H3) ∧ g₀ = 1 ∧ d₀ = 1 ∧ (STK) ∧ …" without TRACK; SD-THM-A
itself and the header verdict carry "on TRACK/on live rows"
correctly.  Display nit only.

**N-3 (NOTE — DRV-NEPS conditioning).**  The composer's DRV-NEPS
family checks companions only on rows where the unique cascade record
was found (`casc_rec is not None`); a hypothetical
cascade-missing g₀=1∧(STK) row would be silently skipped by THIS
family.  It is backstopped: the instrument's SDI-SURV fires
unconditionally on `allg1 ∧ stk ∧ len(casc) ≠ 1` (0 violations), and
the arithmetic 693 = 979 − 286 shows no row was skipped.  Worth one
sentence in the DRV-NEPS bracket; evidence unaffected.

**N-4 (NOTE — cross-file: stale EMPTY header).**  EMPTY_PROOF's own
header still reads "0/1 CLEAN" while its arc stands at 1/2 CLEAN
(PE2 CLEAN, commit 7314525).  This note's "1/2 CLEAN" citation is the
CORRECT one; the staleness lives in EMPTY_PROOF and should be cured
there, not here.

## VERDICT BLOCK

* CRITICAL: none.  Every displayed lemma (SD-L1, SD-L2, (★), SD-L4's
  consumed clauses, SD-THM-A(i)–(v), SD-L5, SD-L6, SD-L7) re-derived
  VALID from the consumed sources; SD-L3's consumption faithful to
  the accepted [RMG] text; the (NEP)-discharge scope exact; no
  m ≥ 3 consumption of the rescoped S-L4(iii) forcing anywhere; both
  boxes honestly open with nothing PROVED consuming them; grade caps
  and consequence displays accurate; both machine legs reproduce
  identically read-only, and three instrument rows re-derived by hand
  agree.
* GAP (1): **G-1** — SD-L4(ii)/(iii)'s "w₀ exactly ŵ / w₀ ≥ ŵ+1"
  clauses need the principal-d-cell pin (false for t ≥ 1 seeds at
  g₀ ≥ 2 where w₀(b_D) = u₀ − t·h₀); claims row and F-A display no
  pin.  No PROVED consumer damaged (both consumption sites sit at the
  principal seed).
* NOTES (4): N-1 (tautological complementarity framing in the
  (SURV-K2) box), N-2 (TRACK elided in two S8 bullets), N-3
  (DRV-NEPS conditioning, backstopped), N-4 (stale EMPTY header —
  cross-file).

Grade consequence if repaired: the gap is a pin-display repair with
no lemma-body mathematics at stake; the notes are disclosures.  This
pass is NOT a CLEAN pass (1 gap); the arc counter stays 0 CLEAN.

SURVDISJ-PE1 FINDINGS: 0 critical, 1 gaps
VERDICT: GAPS-ONLY
