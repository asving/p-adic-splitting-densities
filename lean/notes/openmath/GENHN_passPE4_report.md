# GENHN passPE4 — THE ACCEPTANCE ATTEMPT (2026-08-09, at post-PE3-rider HEAD)

**VERDICT: CLEAN — 0 CRITICAL + 0 GAP + 1 MINOR (+3 observations).
Nothing at GAP-or-worse survived this pass's verification. Clean count
1/2 → 2/2: GENHN is ACCEPTED — text frozen, dated appends only.**

Target: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` at HEAD (rider =
6799e2d dated corrections; body lines 1–1857 byte-identical beadeeb → HEAD —
prefix md5 c38f52834879f76d618b1709146a3991 re-verified this pass against
`git show beadeeb`; PE3 report byte-frozen at 5ea120909ad8c007bbf57aee9c15c475
re-verified; no commit touches the note after 6799e2d). Arc owned end-to-end:
[r1] → [e2] → PE1 (NOT CLEAN 2C/1G/2m; LEMMA GENHN-T(b) REFUTED) → r2 (T(b)′
PROVED) → PE2 (NOT CLEAN 0C/2G/2m) → r3 (item (6) boxed; scoping) → PE3 CLEAN
0C/0G/2m (1/2) → rider (2 dated corrections, minors-only append).

Surfaces this pass owned (never end-to-end before): GENHN.A(i)–(iii)'s own
derivations; the sealed battery's DESIGN (what its 2,223,050 checks assert
vs what GENHN.A/B claim — machine-dark-claim hunt); the [e2]-E2
comp-weighted census general form; the [r1]+[e2]+[r2]+[r3]+rider stack
coherence; the rider itself; free hunt. Fresh route: FIRST f₁ = 4 genre +
first comp = 3 band + rider re-verification + a third iterated key
(disjoint from all five prior instruments).

---

## FINDINGS

### F-1 — MINOR. The [r1] GENHN-ERR-1 residue clause "none is live below
### n = 8" (echoed by [e2]-E2) contradicts the note's own S2
### realizability list; f₁ ≥ 2 stage genres are live at n = 4 and n = 6.

**Quoted claims.** [r1] erratum, RESIDUE paragraph (body L609–611): "The
law's FORM is unaffected (it is stated as the cluster read AT THE NODE,
whatever the node height is), no f₁ ≥ 2 stage genre is machine-exercised,
and none is live below n = 8." Echo at [e2]-E2's honesty clause
(L251–253): "no f₁ ≥ 2 STAGE row is machine-exercised (GENHN-ERR-1's
geography, none live below n = 8)."

**The defect.** Under the note's own vocabulary ("first live n = X" =
realizable at degree X, used at S1/S2/S8 throughout), the clause is false
twice over: (a) genre F = (1, 2, 2) — an f₁ = 2 stage genre — is live at
n = 4 and is MACHINE-EXERCISED (GENH4's committed genre-F keys, consumed
at pin by this very note; E2's own consistency instance IS that genre);
(b) S2's realizability floors display "F3(k) := (Q; 1, 2, 3; k) and
E13(k) := (Q; 1, 3, 2; k) — the f-first siblings" as first live at n = 6
(e₁f₁μ = 6), and passPE1's adopted FR-A geography says "(1,3,2) =
E13(1), first live n = 6" explicitly. The correct scope statement is:
no f₁ ≥ 2 stage row exists IN THIS BATTERY (true — every battery row has
f₁ = 1), the f-first n = 6, 7 genres are visibility-floored beyond the
battery's sweep windows (N ≥ 7; GENHN-BOX-3), and MIXED e₁, f₁ ≥ 2
genres first live at n = 8 — the clause appears to have conflated
"mixed" with "f₁ ≥ 2".

**Failure scenario.** A display-audit consumer trusts the clause and
concludes GENHN-ERR-1's unsettled S-vs-D′h residue (which f₁ ≥ 2
count-side displays substitute the numeric S-node — e.g. GENHN.A(v)'s
"at the S-node") cannot matter below n = 8, so P(6)/P(7)-facing f-first
count displays (E13 at n = 6, 7) are never re-read with D′h; a future
f-first count unit transcribing an S-keyed display then wires the wrong
node height (S = e₁h vs D′h = e₁f₁h — off by a factor f₁) into a sealed
prediction and burns a battery round discovering it.

**Why MINOR, not GAP.** No conclusion is currently priced through the
clause: the residue it mis-scopes is itself declared "NOT settled here"
(the honesty is intact either way); the [r1] node correction D′h + 1 is
displayed and was machine-confirmed at (1,3,2) by PE1 (charge 4); the
n = 6, 7 σ content of the affected genres sits behind [GENHN-HE(3)]
regardless; and every LAW display is node-form-keyed ("at the node,
whatever the node height is"). The defect is one wrong scope clause
inside an erratum's residue paragraph — same species as PE3's F-2.
Cure: one dated line re-reading the clause as "none of GENHN's OWN
machine rows exercises one; mixed e₁, f₁ ≥ 2 first live n = 8; the
f-first genres (1,2,2)/(1,2,3)/(1,3,2) are live at n = 4/6/6 and their
S-keyed display re-read remains owed with the residue."

## OBSERVATIONS (no grade)

* **O-1 (depth-3 floor demonstrated; item (6)(β) corroborated).** The
  fresh route's below-locus n = 16 member (F = Φ₃ᶜ² + 2⁷xΦ′Φ₂ over the
  u₃ = 25 iterated key; p₀ = 95 < 100 = μ₃e₃f₃u₃) has PARI σ
  {(4,1),(12,1)} against the naive dictionary {(16,1)} — the FIRST
  depth-3 demonstration that the tower-node-locus floor is load-bearing
  (PE3's T-FLOOR was depth-2). The floor formula that adjudicates it
  (keep v(Φ₂) exact ⟺ dv₃(Φ₃) > e₃f₃u₃, transported from PE3-R2's
  depth-2 form) is UNDERIVED in the note — exactly item (6)(β)'s honest
  "no proved provenance" — so this is evidence FOR the box's caution,
  not a finding against a claim (the note prices no depth-3 leaf).
  Recorded for the eventual T(b)″ prover.
* **O-2 (instrument-pin hygiene).** The PE1 instrument pair
  (`genhn_pe1_fresh.py` / output) is cited by filename in the [r2] block
  and the PE1/PE3 reports but carries no md5 pin anywhere (battery,
  supp, pe2, pe3 pairs are all pinned). Recorded md5s as of this pass:
  95a38bda5d4a8163bdb628378567bbca / cc911047f2ef6d79780c84a5cceef1fa.
  Not a target finding (the note pins its own artifacts; report
  instruments are the reports' responsibility) — logged for the record.
* **O-3 (battery design notes).** (a) GN-SIGMA's violation RECORDS cap
  at 5 per row (`if nbad < 6`) — the verdict is unaffected (nbad still
  counts; any nbad > 0 is RED), only the printed violation list
  truncates. (b) Cross-degree count-isomorphism (GENHN.CLASS(iii)) has
  machine contact at one genre family only ((2,1,2): GENH4's n = 4 rows
  vs the embedded n = 5 V rows via law_E ties); E31/E3 exist at n = 6
  only in the corpus. Both are inside the proofs' displayed grade;
  neither is an undisclosed machine-dark claim.

## THE RIDER (verified as part of the charge)

* **Freeze mechanics:** body 1–1857 byte-identical beadeeb → HEAD
  (prefix md5 match); PE3 report frozen at its stated md5; sealed
  runners untouched (all pins re-hashed this pass, 100% match).
* **Correction 1 (item (6)(α) mechanism re-attribution):** re-derived by
  hand from scratch — Φ₂² = Φ′⁴ − 8xΦ′² + 16Φ′ + 32 (carry 16x² = 16Φ′
  + 32 with x² = Φ′ + 2); n̂₂(21) = 16Φ′ (21 = 4·4+2·0+5·1, unique in
  range i < 2, b < 2); n̂₂(23) = 16xΦ′ (23 = 4·4+2·1+5·1, unique);
  the u₃ = 23 key's development Φ′⁴ − 8xΦ′² + (16−16x)Φ′ + 32 with
  dv-pins (0,10),(1,8),(2,7),(4,0), the b = 1 pin at 8 > 15/2 (integer
  dv vs half-integral side height — the side-clearing mechanism as the
  rider states it), residual T² + 1 = ψ₂², κ₃ = 23/2 > 8. MACHINE
  (fresh instrument FR3, independent code): development identity exact,
  carrier {(8,1)} both routes, ascent nfeltval (4,10,23) exact, n = 16
  leaf {(16,1)} both routes — every number the rider quotes reproduced.
  The re-attribution itself (carry terms CLEAR the side; cancellation =
  witness arithmetic) is confirmed by the u₃ = 23 key (carry
  UNCANCELLED, still one-sided) and now ALSO by this pass's third key
  u₃ = 25 (carry partially cancelled, −16Φ′ survives at (1,8), still
  one-sided) — the general lemma "carries cancel exactly" is false, the
  side-clearing reading is the right one, and the box's bottom line
  (one-sidedness unproved in general) STANDS.
* **Correction 2 (scope word at 3 echo sites):** the three sites read as
  quoted (S9.1 preamble L1383–1386; GENHN.B depth-split L311–312; title
  rider L53–58); each is a display re-reading only, none carries a
  quantifier, and the r3 full-side scoping they import is the proved
  perimeter (T(b)′'s e₂f₂μ₂ = μ₁ setting line). Coherent with PE3 F-2's
  enumeration; no new text touches the frozen body.

## CLEAN CHARGES (attacked and held)

1. **GENHN.A(i) — S3.1 + LEMMA GENHN-1 with the [r1]/[r2] errata.**
   Invariants re-derived (v(const) = f₁h from the one-sided key polygon;
   η generates F_{Q^{f₁}}; the E3 forcing chain at L/O_L). The corrected
   budget display re-verified at E3 (floors (4,3,3,2,2,1), total 15 =
   2^{24−15} = 512 ✓ P6), E31 ((3,2,2,2,1,1), 11 → 8,192 = 2¹³ ✓ P5),
   GENH4-E ((3,2,2,1), 8 → 4,096 ✓); the node minimum min_i(e₁⌈((μ−j)e₁
   −i)h/e₁⌉ + ih) = (μ−j)S + 1 at f₁ = 1 re-computed (min at i = 1);
   the f₁ ≥ 2 D′h node's consistency with the TRUE floors checked (at
   e₁ = 1 every on-side slot is a consumed lattice pin, floors = side
   height + 1, node = (μ−j)D′h + 1 — PE1's (1,3,2) machine value 7
   re-derived).
2. **GENHN.A(ii) — LEMMA GENHN-2 as main target.** Proof re-derived:
   distinct classes never tie (dv ≡ ih mod e₁, gcd(h,e₁) = 1);
   within-class tie residues Σ_t res(a_{i+e₁t})η^t with a vanishing
   F_Q-combination contradicting [F_Q(η):F_Q] = f₁; residue-of-slot =
   one K-digit; wrap cocycle n(κ)^t = ẑ^{fl}n(tκ) consistent with S4.
   MACHINE (fresh route FR1, first f₁ = 4 contact ever): 26 direct
   nfeltval legs at (1,4,2)/K = F₁₆ including the EXHAUSTIVE 15-subset
   within-class tie census at one height — every nonzero readable
   combination Σ_{i∈S} η^i attained its slot-min EXACTLY (the
   F₂-independence of {1,η,η²,η³} physical at valuation level); offset
   tooth fired 12×.
3. **GENHN.A(iii) — LEMMA GENHN-3 as main target.** (a)–(d) re-derived:
   the undercut floor e₁N; string ends e₁(N−1)+ih; the consultation
   congruence m = e₁k + (i(m)h mod e₁) < e₁N ⟹ m inside the class
   string (checked as arithmetic, both inequalities); carries upward
   from triangularity. E1's trichotomy + the [r2] annex's four-step
   derivation walked: (1) value stability at m = N from η-independence
   (unread components join on complementary basis elements only), (2)
   trichotomy transport verbatim at m = N, (3) deeper band heights
   value-unstable → DRAIN, (4) instances. MACHINE (FR2): FIRST
   comp = 3 contact — at (1,4,2), N = 9, all Q³−1 = 7 nonzero readable
   triples decide RAM(9) → {(2,4)} (14 jobs incl. out-of-window
   δ-perturbations, both routes), v(A₀(θ)) = 9 for every lift
   (nfeltval); the deeper-band undercut is REAL (v = 10 vs 9 across
   lifts of the readable-first-at-10 member — annex (3)'s drain is
   necessary, demonstrated).
4. **[e2]-E2 general form (charge surface 3).** The census clause's
   derivation from the slot model is complete AT ITS STATED SCOPE:
   the [r2] annex derives it at (μ = 2, e₁ = 1, f₁ ≥ 2, all k), the
   e₁ ≥ 2 mixed genres are excluded by E1's exclusion list (the annex
   says so explicitly and claims only lift-stability content there),
   and comp(m) is defined from GENHN-2 alone. Machine contact now
   spans comp = 1 (GENH4 (1,2,2) @ pin), comp = 2 (PE1 FR-A), comp = 3
   (this pass) — census Q^{comp}−1 exact at all three.
5. **GENHN.C at a FOURTH genre — (1,4,2), first f₁ = 4 σ contact.**
   Dictionary {(2,4)} / {(1,4),(1,4)} / {(1,8)} confirmed on 24 scored
   jobs, BOTH oracle routes, disc ≠ 0 each: RAM(9)/RAM(13) (odd-u
   one-side), 2SIDED (u > 2w), SPLITEQ vs INERT adjudicated by GENUINE
   F₁₆ residual arithmetic — Tr_{F₁₆/F₂}(η) = 0 → splits →
   {(1,4),(1,4)}, Tr(η³) = 1 → irreducible → {(1,8)} (hand-derived
   traces, PARI adjudicated; swap tooth fired 2/2), SPLTAIL corner
   (A₀ = 0, f = Φ′(Φ′+A₁)) exact. The S7 trichotomy's silent steps
   re-derived: the norm-count even split (Res(F,Φ′) = ±Nm(A₀), j(2w−u)
   = D′(2w−u), u ≠ 2w ⟹ j = D′), the [r2] RAM lcm rider
   (lcm(e₁, 2e₁/gcd(u,e₁)) = 2e₁, gcd odd), Galois-invariance of
   v(Φ′(θ)) on an irreducible block.
6. **The sealed battery's design (charge surface 2).** Line-level
   structure read (families, laws, readers, oracle, main): each family
   asserts what S11.B claims — GN-CLASS = CLASS(i)/(ii) realizability
   grammar at all depths + flagship entry-law values + PREDICTED-ABSENT
   + the n = 5 pinned-reader tie; GN-LAWTIE/GN-STAGE2 = A(v) at three
   genres both directions (re-based law × sibling fiber); GN-FIB =
   A(i) budgets/nodes pointwise; GN-E3 = the μ = 3 partition + laws;
   GN-REFINE3 = A(iv)'s compensating instrument (actual re-division);
   GN-TOWER = T(a) only (witness + zero-CS census + min-n scan);
   GN-SIGMA = C's dictionary on the certified perimeter with the
   uncertified tail measured-not-scored. law_Egen re-audited: TRUE
   floors (f₁ = 1 corrected-budget form), INERT census q(q−1)/2 =
   #(monic irreducible quadratics/F_q), internal partition assert
   Σ = q^{#slots}; scoring honest (any nbad > 0 is RED; GREEN ⟺ 0
   violations ∧ all teeth). MACHINE-DARK HUNT: every dark surface found
   maps to a DISCLOSED box — f-first rows (BOX-3 + S9.2 item 4), mixed
   (2,2,2) (BOX-3), tower count laws (TOW-1 item 1), d ≥ 2
   (GENIND-BOX-3), q = 4 F-kit (Q22 inherited), μ = 3 σ (labeled
   corroboration of the open [GENHN-HE(3)], never scored as proof).
   No UNdisclosed machine-dark claim survived the hunt; the scorecard
   cross-ties recomputed independently (12,288 = 4,096·3 = law_E ×
   (q−1)(q^{N−3}−1); 8,192 = 2^{24−11}; 4,374 = 2·3⁷ at N = 3;
   512 = 2^{24−15}; 39,366 = 2·3⁹ at N = 4; P9's 37,792 = the six
   batch sizes summed).
7. **Cross-round stack coherence (charge surface 4).** The floor/node
   chain is consistent across all five layers: [r1] D′h node (level 1)
   ↔ [r2] TRUE budget floors (node re-derivation matches) ↔ T(b)′'s
   inner floor u₂ > e₂D′h (PE2 charge 1: the lift terms clear Φ₂'s side
   by exactly that) ↔ item (6)(β)'s κ₃ > dv₂(x^{D₂}) witness floor ↔
   the depth-2 composed floor e₂f₂u₂ (PE3-R2) whose depth-3 transport
   this pass demonstrated (O-1). Grade lines consistent (title 0/2 +
   r2/r3 riders + PE3's 1/2 carried by the dated append); the S10 arc
   lines match the actual reports' verdicts; T(a) untouched by the
   T(b) refutation as claimed (entry pins below the correction floor —
   PE1's mechanism, re-checked against the P8 witness data).
8. **GENHN-T(a) + realizability floors.** μ ≥ 4 criterion from
   GENIND.A(IV) inside the stage (abscissa budget e₂f₂μ₂ ≥ 4);
   n ≥ e₁f₁μ ≥ 8; μ = 2 exhausts n = 4, 5 (products 4 or ≥ 6); the
   n = 8 realization arithmetic; my (1,4,2) legs are themselves a
   first-live n = 8 f-first instance consistent with CLASS(ii).
9. **Item (6)'s iterated-key grammar at a THIRD key (new instance).**
   u₃ = 25: n̂₂(25) = 32Φ′ (25 = 4·5+2·0+5·1, unique in range — checked
   by exhaustion), Φ₃ᶜ = Φ₂² − 32Φ′ = Φ′⁴ − 8xΦ′² − 16Φ′ + 32
   (identity exact), one-sided slope 5/2 with residual ψ₂², carrier
   {(8,1)} both routes, ascent (4,10,25) exact, on-locus leaf RAM(103)
   → {(16,1)} both routes. Third confirmation of the box's derived
   grammar (all with ψ₃ linear — PE3's R1 f₃ ≥ 2 disclosure stands).

## MACHINE LEG (integrity)

* **Pins — 100% match (re-hashed this pass):** genhn_checks.py
  637427dc…, artifacts dd9edbea… / 7d4a3e86…, genhnr2_supp.py
  51154c95… + output 664036bc…, genhn_pe2_fresh.py 4a28246e… + output
  10b685b0…, genhn_pe3_fresh.py f70d3d56… + output b484e7fa…, and the
  seven S11.A supplier pins (genind e7ca150b…, genh4 ee8024b7…,
  qscout22 cb885663…, w10 a9c34244…, w12 7dc040d9…, genind results
  366f2143…, qscout22 results 6c2441a1…).
* **Isolated re-runs (fresh dir /tmp/genhn_pe4_iso, 12-module import
  closure + 3 pinned jsons, all five instruments, this pass's own
  runs):** sealed battery **GREEN — 2,223,050 / 0, teeth 2/2/2/2/1,
  449.3 s**, results JSON content-identical to the committed artifact
  except `elapsed_s` (449.3 vs 450.0), V p=2 diagnostic tail 1,216/349
  reproduced; genhnr2_supp GREEN 147/0; genhn_pe1_fresh GREEN
  (FR-A 2 / FR-B 68 / FR-C 84 / FR-D 21 / teeth 10, refutation tallies
  reproduced); genhn_pe2_fresh GREEN 219/0; genhn_pe3_fresh GREEN
  176/0 — each output identical to its committed artifact modulo
  timing figures only. Exit 0 all five.
* **Tautology audit (this pass's instrument):** predictions
  hand-derived in the docstring; PARI is the only oracle, on TWO
  routes (route A = factorpadic + lift + nfinit([g,[2]]) +
  idealprimedec; route B = global factor + same); slot legs compare
  the note's formula against nfeltval directly; teeth mutate the slot
  formula (T-SLOT-OFF ×12), the σ dictionary (T-DICT-F16 ×2), and the
  locus floor (T-FLOOR3 ×1) and demand refusal. No imports from any
  prior GENHN runner.

## FRESH ROUTE (disjointness + verdict)

`verification/openmath/genhn_pe4_fresh.py` (md5
f99365bccead513f641fe25bcb933f02, artifact 04ae054c…): **GREEN — 145
checks / 0 violations, teeth T-SLOT-OFF ×12, T-DICT-F16 ×2, T-FLOOR3
×1.** Territory never touched by the battery (f₁ = 1 rows), PE1
((1,3,2) + (2,1,4) refutations), supp (outer-f₁ = 1 towers, u₃ = 21),
PE2 (outer-f₁ = 2 towers, Q = 4), or PE3 (e₂ = 3, p = 3/F₉, u₃ = 23):
FIRST f₁ = 4 stage genre ever ((1,4,2)/F₁₆, first-live n = 8 f-first);
FIRST comp = 3 band census; FIRST K = F₁₆ residual σ-decision
(trace-criterion, PARI-adjudicated); the rider's u₃ = 23 data
re-verified by independent code; a THIRD iterated key (u₃ = 25); and
the FIRST depth-3 floor demonstration (O-1). RUN-1 DISCLOSURES (in the
instrument docstring, none touching a note claim): two hand-prediction
slips in my own fixed slot legs caught by the instrument's pre-oracle
assert; a whitespace-normalization bug scoring 46 spurious mismatches
whose values all agreed; and my own depth-3 floor mis-set (p₀ > 50 vs
the correct p₀ > 100) — located by re-derivation, corrected, and
re-purposed as the T-FLOOR3 tooth. Not attempted (disclosed): e₁ ≥ 2
mixed f₁ ≥ 2 genres (n = 8 mixed — no note claim to test beyond the
boxed surface); f₃ ≥ 2 third-stage keys (PE3 R1's disclosure stands);
d ≥ 2 ambients.

## GRADE LINE

**passPE4 = CLEAN under the charge bar: CRITICAL ×0, GAP ×0, MINOR ×1
(F-1: the "none live below n = 8" scope clause in [r1]-GENHN-ERR-1 +
its [e2]-E2 echo, contradicted by the note's own S2 realizability list
— one dated-append line owed, no theorem/count/σ moves). Clean count
1/2 → 2/2: GENHN ACCEPTED at 2/2 — the note text is FROZEN (body
byte-frozen at prefix md5 c38f5283…, dated appends only from here),
sealed runners and artifacts byte-frozen at their pins.** What the
acceptance pass positively establishes: GENHN.A(i)–(iii)'s derivations
held as main targets (with first f₁ = 4 / comp = 3 / F₁₆ machine
contact); the battery's design asserts what the note claims and hides
no undisclosed machine-dark claim; the [e2]-E2 census general form is
derivation-complete at its stated scope with contact now at comp ∈
{1,2,3}; the five-layer repair stack is mutually coherent; the rider's
two corrections are exact (Correction 1's data reproduced by
independent code); and GENHN.C extends to a fourth genre exactly as
displayed. The one MINOR is queued for the orchestrator's dated-append
fold (the F-1 cure line above); the acceptance stands per the HEX3
minors-only precedent. Consumers: GENIND/PROJECT_STATE inherit "GENHN
ACCEPTED 2/2" — orchestrator's fold, flagged here.
