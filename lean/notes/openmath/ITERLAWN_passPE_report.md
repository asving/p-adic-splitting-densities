# ITERLAWN pass PE — Fable round-1 hostile pass (execution + content) on ITERLAWN_PROOF_2026-08-08.md @ 4df7fdb

**FINDINGS: 0 critical, 2 gaps (+2 nits); VERDICT: NOT-CLEAN (0C/2G) — both
gaps narrow display/citation-discipline findings; the mathematics of the
level-generic inductive step survived a full hand re-derivation AND a
from-note reimplementation at 22,369 family-checks / 0 violations on nine
fresh instances including the first 6-read data; every consumption is legal;
the acceptance counter does NOT advance (round 1 of the 2-clean bar).**

Verifier: Fable (ITERLAWN-PE), fresh context, wallclock 2026-08-03 (campaign
2026-08-08). Target: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` at
4df7fdb (1,067 lines, including the r38 S7 dated bracket). Charge: the S10
suggested charges (ii) execution [F2c genre] + (i) content + (iii) rule-8,
per the wave-20 orchestrator brief.

---

## 1. EXECUTION LEG

### 1.1 Diag re-run (byte-exactness)

`verification/openmath/iterlawn_diag.py` re-run on this machine:
**exit 0, BYTE-EXACT vs `iterlawn_diag_output.txt`** (`diff -q` clean),
wallclock 2.5 s (matching the note's S8 claim). md5s match the note's S8
declarations exactly:

    cd7581b7fd9df555e517b69556199ef3  iterlawn_diag.py       (note: cd7581b7...)
    7c72c4c6c0a953ebd41a56eab1e266e1  iterlawn_diag_output.txt (note: 7c72c4c6...)

Output counts re-verified against every S8 display: A1_casc 464, A2_star
464, A3_rho 36, A4_dcx_law 35 (= 28 A4-row + 7 C3-row + 0 B4-row outer-locus
pairs, law exact on all), A5_e1pass 144, B1_L6 56, B2/B2'/B3/B4 all 544,
B4_star 544, B5 24+56+224, B6_topcontrol 128, B6 passthroughs
416+128+416 = 960, T5B censuses 16 sharp-DCX₂/48 outer per instance, T5C
4 outer/0 sharp. Family-check total 5,311 = the note's "~5,300". ZERO
violations; DIAG VERDICT: CLEAN. Diag source provenance (opened only AFTER
the reimplementation below was written and frozen, per the F2c discipline):
sealed artifacts consumed via read-only imports (`grb_order2_check`,
`strata3_probe`, `iterlawr_probe`, `iterlaw4_probe`); `git status` shows no
tracked-file modifications; deterministic (no sampling, no seed); verdict
logic exit-coded on the violation list.

### 1.2 F2c leg: from-note reimplementation on FRESH instances

`verification/openmath/iterlawn_pe_reimpl.py` (md5
cae45db2318b89520dd5484466ef3604) + frozen output
`iterlawn_pe_reimpl_output.txt` (md5 cfad79439821551f9c6a572f5d627d0b) —
written FROM THE NOTE ALONE (S0.1/S0.2/S0.3/S2/S4.0–S4.7/S6.3/S6.4), before
re-opening `iterlawn_diag.py`; zero code shared with the diag or the sealed
harness (own ring classes ℤ_p and F_p[[t]], own nested-extension residue
fields with extended-Euclid inversion, own reads/realize/split/anchor
stack). The note's displays were sufficient to rebuild the ENTIRE calculus
from scratch — including the canonical ε-corrected lifts via REALIZE-(m)
and the (RM-m)/DCX engine objects (R, Q by monic division) — with no appeal
to any sealed source: an F2c pass in the strict sense.

**Fresh instances (own seed; shapes disjoint from the diag's A4/B4/C3 reuse
and its T5A/T5B/T5C).** Sampling: one smallest in-window representative per
residue class mod E_{n+1} (justified by the S2 descent lemma), full ordered
W1×W1 blocks. Format (e,h,g) per read:

| id | ring | d₀ | reads j=0.. | E | rung | pairs | live strata |
|---|---|---|---|---|---|---|---|
| I4A | ℤ₂ | 1 | (2,1,1)(2,1,1)(1,1,2)(3,2,1) | 12 | 3 | 144 | II-1/2/3 @ m=2 (27/9/18); h-mix top (3,2) |
| I4B | ℤ₃ | 1 | (3,2,1)(2,1,1)(1,1,2)(2,1,1) | 12 | 3 | 144 | **DCX₂-LIVE: 4 detector fires = 4 sharp pairs** |
| I4C | F₂[[t]] | 2 | (2,1,1)(1,1,2)(2,1,1)(2,1,1) | 8 | 3 | 64 | II-1 @ m=3 (16) → RM-2 calls; order-15 letter |
| I5A | ℤ₃ | 1 | (3,2,1)(2,1,1)(1,1,2)(2,1,1)(1,1,1) | 12 | 4 | 144 | **DCX₂-LIVE (4)** + II-1@m=4 (36) → RM-3 + e₄=1 tie |
| I5A | F₃[[t]] | 1 | same | 12 | 4 | 100 | DCX₂-live (1); ring replicate |
| I5B | ℤ₃ | 1 | (2,1,1)(1,1,1)(3,1,1)(1,1,2)(2,1,1) | 12 | 4 | 144 | **level-3 MIDDLE CASCADE chain m=1→2→3**: II-1/2/3 @ m=3 = 36/12/12 fed by II-3 @ m=2 (36); live top e₄=2 |
| I5B | F₃[[t]] | 1 | same | 12 | 4 | 100 | cascade replicate (15/5/8 @ m=3) |
| I5C | F₂[[t]] | 2 | (1,1,2)(2,1,1)(2,1,1)(1,1,2)(2,1,1) | 8 | 4 | 64 | **e₀=1 ∧ d₀=2**: 16 RM-1 calls INSIDE the fenced DEV-1 corner; II @ m=3 (12/4/8) |
| I6S | ℤ₃ | 1 | (2,1,1)(1,1,1)(2,1,1)(1,1,2)(1,1,1)(2,1,1) | 8 | 5 | 36 | **6-read SMOKE — first 6-read data ever**; II-3@m=2 (9), II@m=3 (3/1/4); law 36/36 |

**Result: exit 0, ZERO violations across 22,369 family-checks on 940 pairs
(9 instance rows).** Per-family actuals (baseline, totals):

    K1  SHIFT-(n) cascade beta_j'' = B_j + S_j, all levels:   3,444/0
    K2  D_j-INT (exact divisibility, all levels):                940/0
    K3  (STAR)-POS (S_j = 0 or e_j S_j >= gamma_{j+1}):        3,444/0
        [equality e_j S_j = gamma_{j+1} attained 0 times — the bound
         is never tight on this data; see nit N2]
    K4  WINDOW-(n):                                              940/0
    K5  L6-(n) anchor = eps-chain, w = gamma:                    940/0
    K6  W-MULT top (P-WM: z-top factor + single slot + w):       940/0
    K7  THE LAW c_{n+1} = zbar^delta prod z_j^{D_j}:             940/0
        (931 off-DCX exact + 9 ON-DCX pairs ALSO exact — fresh
         instance evidence for the open (W-MULT-DCX) corner)
    K8  (P-DS) at EVERY rung r: slot support in {S,S+1}, E0 != 0,
        w(E0) = B_r, certified read, E1 weight clause, E1 => CII_r:
        3,421 rung-checks + 711 E1-clauses / 0  (23 skipped on-DCX)
    K9  CASE-SPLIT-(n) exactly-one + (Case I <=> deg A < deg Phi): 2,490/0
    K9b II-leg substitution identities (E0new/E1new = the S4.6
        displayed R/Q combinations, exact polynomial identity):    466/0
    K10 DCX detector == [IL3] sharp form (m=2, both directions):   940/0
        DCX_m => outer-bound predicate:                              9/9 in-bound
    K11 (RM-m) box instance checks (R,Q weight clauses + the
        z^{eps'} read clause) at every fired engine call:
        RM-1 308 (+16 IN the fenced e0=1∧d0>=2 corner) / RM-2 158
        / RM-3 52  — ALL clauses hold, 0 violations
    K12 descent phi_{g+E} = pi phi_g 90/0 · rho monodromy 90/0 ·
        constants mod-E invariance 90/0
    K13 e_{j-1} = 1 passthroughs (D_j = 0, S_{j-1} = S_j):       1,320/0
    K15 e_top = 1 two-way tie (constants AND value, vs an
        independently rebuilt truncated tower):               244 + 244/0
    (I_m) descent-invariant asserts inside REALIZE (every
        recursive call, all tower builds):                        94/0
    REALIZE R1/R2/R3 clauses via the independent read stack:      38/0

**DCX geometry actuals.** Detector (second-round Q¹-overflow, computed by
actual division against Ĉ_{m−1}) fired 9 times, all at m = 2, all on e₀ = 3
towers, all EXACTLY on the [IL3] sharp set (K10: 940 pairwise
detector==sharp agreements, zero mismatches) — the m = 2 sharp form and its
e₀ ≤ 2 emptiness confirmed on fresh seeds. At m = 3 the outer locus is
POPULATED (10 pairs across I5B/I5C/I6S) but the detector never fires — all
these towers have e_{m−2} ≤ 2 there, so this is consistent with (and mild
fresh evidence for) the S4.7 CONJECTURE DCX_m = ∅ unless e_{m−2} ≥ 3; no
refutation found. The law held on ALL 9 detector-DCX pairs (K7's on-DCX
side-count), extending the note's B7 instance evidence to new seeds.

**RM-family actuals (the open engine, instance-probed).** 534 engine calls
total; the box's THREE claims (w(R) ≥ λ+γ_{m+1}; w(Q) ≥ λ+γ_{m+1}−w_mΦ_m
when Q ≠ 0; R-read = z_m^{ε′}·v·τ_m with the exact EPS-carry ε′) checked at
every call INCLUDING the read clause on E₁-inputs (which the note's
consumers use only weight clauses of): 0 violations. Notable: RM-2 (158)
and RM-3 (52) are, to my knowledge, the first instance data ever taken on
the m ≥ 2 open family in box form; and the 16 RM-1 calls on I5C land INSIDE
the fenced {e₀=1 ∧ d₀≥2, j ≥ g₀} DEV-1 corner (products reach Φ₀-exponent
3 ≥ e₀g₀ = 2) — the box held there too. Instance evidence only; no grade
upgrade implied.

**Mutation controls: 7/7 visible AND caught** (subset I4B@ℤ₃ + I4C@F₂[[t]];
visibility = counted pairs/calls where the mutated formula provably changes
the checked value; caught = ≥ 1 violation raised):

    M1 D_j drops l_{j-1}S_j        vis  41  viol 181  CAUGHT
    M2 SHIFT drops S_j             vis  41  viol  93  CAUGHT
    M3 composed-shift sign flip    vis  20  viol  36  CAUGHT
    M4 law top delta -> 1-delta    vis 128  viol 127  CAUGHT
    M5 (RM) read clause drops eps' vis   9  viol   9  CAUGHT
    M6 rho exponent sign flip      vis   8  viol   8  CAUGHT
    M7 (P-DS) E1 bound +1          vis  56  viol  56  CAUGHT

(M4's 128 vs 127: the one visible-but-not-violating pair is a DCX pair in
the mutated subsample, where a law mismatch is routed to the on-DCX
side-counter rather than the violation list — the catch is real on the
other 127.) Design note: an earlier candidate mutation "tighten (★) by +1"
is INVISIBLE on all data (equality is never attained; nit N2) and was
replaced by M6 — visibility pre-verification did its job.

**Iteration disclosure (hostile-pass hygiene).** Two design iterations, both
on MY side, neither a note defect: (1) first-draft W1 sampling (smallest N
in-window γ) hit only even residues on I4B, silently emptying the δ = 1
strata — replaced by per-residue-class sampling; (2) first-draft seeds used
h₀ = 1 everywhere, which makes the sharp-DCX₂ inequality S₁ + s(γ₂) ≥ 2e₀
arithmetically unsatisfiable (s(γ₂) = 1 forces S₁ ≥ 2e₀−1 > 2e₀−2) — the
DCX₂-live goal needs h₀ = 2 seeds, matching the diag's T5B design. Both
iterations changed instance selection/sampling only, never a checker
formula.

---

## 2. CONTENT LEG (hostile line-audit of the generic step)

Full hand re-derivation performed of: SHIFT-(n)/D_j-INT interleave (verified
non-circular: SHIFT at j needs only D_j-INT at j, whose proof needs only
SHIFT at j, both from β_j″ = B_j + S_j already in hand); (★)-POS both
branches including the active-case chain e_{j−1}S_{j−1} ≥ (g_{j−1}−1)e_{j−1}γ_j
+ γ_j + h_j/e_j > γ_j; WINDOW-(n) including the S₁ > (e₀−1)h₀ worst-case;
EXP-KIT (a)/(b)/(c); TRUNC; REALIZE-(m) with the (I_m) descent chain
γ⁽ⁱ⁾ ≥ γ_m/e_{m−1} > e_{m−2}g_{m−2}γ_{m−1} and the m = 1 admissibility
u(β) > (g₀−1)h₀; WELL-DEF (i)/(ii); L6-(n) degree telescope
(Σ(e_j−1)deg Φ_j telescopes against deg Φ_{j+1} ≥ e_j deg Φ_j); CASE-SPLIT
exhaustiveness/disjointness; Case I including the g_{n−1} ≥ 2, δ_n = 1
sub-branch (single coefficient lands at grid slot j = δ_n^pl, matching
(P-WM)); II-1/II-2/II-3 line tables term-by-term — slot k attained at B_n,
slot k+1 ≥ B_n + h_{n−1} (both the Q⁰ and R¹ routes), slot k+2 ≥ B_n +
2h_{n−1} with the e_{n−1} ≥ 3 off-grid forcing, the e_{n−1} ∈ {1,2}
collision legs via READ-ADD, the ε′-carry/canonical-lift cancellation
ε_{n−1}(B+γ_n) = z^{−ε′}ε(B)ε(γ_n) against τ = ε(γ_n)^{−1}c, and the II-1
e_n = 1 read-0 leg by the corrected inequality B_n − γ_{n+1} < B_n −
e_{n−1}γ_n (checked: it does NOT inherit the [IL3] PC2-F1/PE2-F1 display
defect, as the header claims); S5 assembly (one EXP-KIT(c) kernel per level,
T = S_j, no cross-level denominators); the S2 slotwise-cocycle and descent
lemmas; COR-1..5 including the ρ display. The (ITER-PKG-r) closure audit:
each of (P-L6)/(P-WM)/(P-DS) is re-established at rung n in every leg — no
step consumes more of the IH than the package states (checked leg-by-leg
against the (P-L6)/(P-WM)/(P-DS) clauses; the only inputs are TRUNC,
READ-ADD, WELL-DEF Ĉ-clauses, EXP-KIT, and the (RM-(n−1)) call, all
displayed). The (RM-1) box's double-sum factoring was verified as a genuine
derivation (DIGIT-SPLIT children stay < 2e₀g₀; on-line pairs factor because
K₀ is a field, i.e. Gauss/no-zero-divisors; the exponent additivity is L1).

**FINDING G1 [GAP — grade-label understates a conditionality].** The DCX
outer bound is graded "PROVED, generic" with no IH qualifier — S0.3 status
table row "DCX-(n): outer bound per level | PROVED, generic | S4.7", the
S0.3 excluded-locus bullet "outer bound proved generically", and S4.7
"Outer bound (PROVED, generic — from the S4.6 slot arithmetic alone)". But
the displayed proof consumes the IH (P-DS) clause explicitly ("needing
E₁ᴵᴴ ≠ 0 (⟹ CII_{m−1}, ⟹ g_{m−2} = 1 by (P-DS))"), and (P-DS) at rungs
≥ 3 sits inside the (RM)-conditional package chain — the neighboring
CASE-SPLIT row honestly carries "(given IH package)", the outer-bound rows
do not. Consequence: the outer bound (and the "DCX_m = ∅ whenever
g_{m−2} ≥ 2" emptiness leg that rides it, cited at S8's T5A gloss) is
conditional exactly like rows 5/6 unless one adds an argument that the
support/E₁/CII sub-clauses of (P-DS) are engine-free (plausible — the E₁
constructions never call the engine and deg Q < deg Φ is automatic from
division — but that argument is NOT in the note). Cure is one qualifier
token at three sites, or the short engine-free-support lemma. NOT critical:
the S0.3 "Unconditional at every rung" bullet correctly omits the outer
bound, and no downstream clause consumes it as unconditional.

**FINDING G2 [GAP — rule-8 citation discipline, the note's own S10(iii)
standard].** The note pledges the [IL3] grade "at EVERY consumption"
(header) and its own suggested audit demands the block at "every [IL3]
mention" (S10(iii)); 7 of the 59 [IL3] mentions carry NO grade/package
token at the mention site: line 98 ("applied proactively as in [IL3]
S0.1"), line 107 ("as in [IL3] S0.2"), line 246 ("priced as a DEV-2 unit
([IL3] S4.7)"), lines 418/423/452 (S4.1: REALIZE m = 1 base = "[IL3]
WELL-DEF(i)'s display" / "(ii) verbatim" — the one SUBSTANTIVE consuming
site in this list), line 762 ("rung 2: [IL3] S4.7's roster-B evidence"),
plus the S6.3 lesson-glosses (lines 796/816/830/837/838) and the S8/S10
procedural name-drops (944), which I read as non-consuming provenance. No
grade MISSTATEMENT anywhere — the S7 ledger rows and the S0.3 table carry
the [IL3] conditionality for every affected clause (row 3 covers the S4.1
site), and the r38 bracket's supersession clause cures the grade WORDING
note-wide — but the bracket does not retroactively place tokens at naked
sites, and rule 8 as the note itself states it is per-mention. Same genre
and severity as the PE2/PC2 "residual citation token" findings on [IL3].

**Nits (no grade impact).** N1: Case II-3 ends without displaying its
(P-DS) E₁-export weight clause (w_n(E₁ᴵᴴ) as a level-n digit ≥ B_n −
e_{n−1}γ_n + h_{n−1}; one line, follows from the S4.4 weight display) —
II-2 says "exports as displayed", II-3 doesn't. N2: (★_j)'s nonzero branch
e_jS_j ≥ γ_{j+1} is never TIGHT (equality forces e_j = 1 ∧ carry 1, which
the e = 1 grid kills; 0 equality instances in 3,444 checks) — correct as
stated (≥ holds), but a sharper display (≥ min(2γ_{j+1}, …)) is available
if ever needed. Also noted: the S_j symbol is overloaded (composed shift in
S0.3/S2 vs slot-sum s_j+s_j′ in S4.4–S4.6/(P-DS)) — defined at each use,
reader hazard only, same convention as [IL3].

## 3. CONSUMPTION-LEGALITY VERDICTS (all LEGAL)

* **[IL] (rung-1 base): LEGAL.** ACCEPTED artifact consumed as proved;
  the acceptance package pasted at the header and at 7 full-paste sites,
  ALL byte-identical (whitespace-normalized) to the ledger block
  "ITER-LAW ACCEPTED — 2026-08-03" (BRIDGE_ADJUDICATIONS:6643); mentions
  not carrying the full paste carry the compressed form + a header
  pointer. [IL]'s display verified to BE the n = 1 unrolling of the S0.3
  recursion (ITERLAW:90–95: c = z̄^{δ₂}·z₁^{(s₁-defect+ℓ₀γ₂δ₂)/e₀} =
  δ, S₁ = γ₂δ₂, D₁), as S5 claims; the E₂-superset erratum wording
  matches the package.
* **[IL3] (rung-2 link): LEGAL, two-phase.** At composition: consumed
  CONDITIONALLY at its then-true grade (0/2, round-2 not-clean), threaded
  through S7 with the failure-propagation display — never consumed as
  proved. Post f726b36: the r38 S7 bracket upgrades the link; its pasted
  defined-term block is byte-identical (whitespace-normalized) to the
  ledger block "[IL3] ACCEPTED — 2026-08-03" (BRIDGE_ADJUDICATIONS:7902);
  the acceptance commit and arc (PC3 5bdca01 + PE3 f288b73 on a687b80 →
  f726b36) verified in git history. The bracket's supersession-of-dated-
  history device is legitimate latest-display practice; residual naked
  mention sites are G2 above.
* **(RM-m, m ≥ 2) and (W-MULT-DCX-m): LEGAL as OPEN.** Boxed, priced,
  consumed visibly at exactly the S4.6 II-legs and the S4.7 DCX row;
  no proved-generic leg silently consumes them (grep + hand audit of
  S2/S3/S4.0/S4.1/S4.2: engine-free; L6-(n) verified to consume only
  TRUNC + degree telescope + IH(P-L6), exactly as claimed). Sole
  qualifier miss is G1 (outer bound), which is an IH-package
  conditionality, not a silent RM consumption.
* **(RM-1) via [IL3]: LEGAL and the dictionary is EXACT.** The box's
  read clause R_{m,λ+γ}(R) = z_m^{ε′}·v·τ_m with ε′ = ⌊(s_m(λ)+
  s_m(γ_{m+1}))/e_{m−1}⌋ is [IL3]'s displayed computations on the nose:
  S4.5 "R_{1,β*}(Rem) = z₁^{δ₁+ε′}τ" (= z₁^{ε′}·v·τ with v = z₁^{δ₁},
  the rung-1 certified read of a) and S4.6 "R_{1,β*}(Rem⁰) = −c₀τz₁^{ε′}"
  (v = −c₀ = z₁^{δ₁}); same ε′ definition, same EPS-MULT cancellation
  ε₁(β*)ε₁(γ₂)^{−1} = z₁^{−ε′}ε₁(B₁), same Q-weight clause, and the
  generic II-2 "k+2 ≤ e_{n−1}−1 forces e_{n−1} ≥ 3" is [IL3]'s N3
  vacuity transposed level-generically. Scope inheritance verbatim from
  the [IL3] DEV-1 erratum (e₀ ≥ 2 step; e₀ = 1 base range; d₀ = 1 junkΦ
  ≡ 0; the fenced corner {e₀=1 ∧ d₀≥2 ∧ j≥g₀} displayed). What the box
  ADDS over [IL3] — the double-sum factoring extending monomial inputs
  to general digits f — is displayed with a complete argument that I
  verified independently (see §2). The n = 2 specialization display
  (S4.6 close) is clause-for-clause correct, and at n = 2 the generic
  legs only ever feed the engine monomial-shaped rung-1 exports, i.e.
  the exact inputs [IL3] proved.
* **L3CONVERGENCE: LEGAL.** Consumed only as the statement source; the
  S2 Candidate-2 recursion (L3CONVERGENCE:166–176) is VERBATIM the S0.3
  display (same S_n seed, same D_j/S_{j−1} lines, same product form),
  and the owed status upgrade is correctly deferred to this note's
  acceptance (S10). The refuted naive template (D₁ = defect+ℓ₀γ₂δ₂ at
  n ≥ 2) is not used anywhere in the note.
* **ITERLAW4_PROBE (rung 3): LEGAL as instance evidence only.** The
  verdict block (ITERLAW4_PROBE:539-541) says "MEASURED LAW
  (instance-confirmed conjecture, 0 violations on 362,624 samples, 72
  fresh towers, 4 rings) ... rung n = 3 MEASURED GREEN ... No proof
  claim"; F-SUB 2,896/0 at :483; the charter sentence "the general-n
  compose (L6-(n) + W-MULT-(n)) is the chartered next unit" verbatim at
  its close — all three quotes match the note's citations; the note
  never promotes rung 3 above MEASURED (S0 rung ledger, S7 rows 8/11).
* **Sealed artifacts: read-only respected** (diag imports; no tracked
  file modified; my pass adds only its own new files).

## 4. RULE-8 AUDIT SUMMARY

[IL]: 59-site sweep — every mention carries ACCEPTED + package (full paste
×7, byte-identical to ledger; compressed-form + header pointer elsewhere).
PASS. [IL3]: 59 mentions; grade tokens present at all consuming sites
EXCEPT the seven listed in G2 (one substantive: S4.1 REALIZE m = 1 base).
The r38 bracket's rung-ledger paste and defined-term block match the
ledger byte-for-byte. FAIL-NARROW (= G2). The e_{m−2} ≥ 3 statement is
labeled CONJECTURED at both display sites (S4.7 bullet, S0.3 table row)
and never consumed as proved; S8/B7 and my fresh data are cited/reported
as evidence only. PASS.

## 5. PROVENANCE APPENDIX

Repo state: branch main @ 4df7fdb (target note byte-frozen; verified
`git status` clean on tracked files before and after execution). Files
PRODUCED by this pass (the only writes):
`verification/openmath/iterlawn_pe_reimpl.py` (md5
cae45db2318b89520dd5484466ef3604, 1,051 lines),
`verification/openmath/iterlawn_pe_reimpl_output.txt` (md5
cfad79439821551f9c6a572f5d627d0b), this report, and the ledger append.

Tail of `iterlawn_diag_output.txt` re-run (byte-exact, eyeballed):

    == VIOLATIONS: 0 ==
    total elapsed 2.5s
    DIAG VERDICT: CLEAN

Tail of `iterlawn_pe_reimpl_output.txt` (eyeballed):

    == VERDICT: baseline violations = 0; mutations caught+visible = 7/7; elapsed 7.0s ==
    REIMPL VERDICT: CLEAN

Ledger slices verified byte-identical to the note's pastes (whitespace-
normalized; mechanical diff, not eyeball): the [IL] scope sentence
("Scope as accepted: the harness tower class (superset of DITER_RESTATE
§S2's E₂ > 1 pin; on-the-nose coincidence restricted to E₂ > 1);
residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂)
wrapper rides the accepted GRB retarget; orders ≥ 3 untouched") at
BRIDGE_ADJUDICATIONS:6655–6658 vs 7 note pastes; the [IL3] defined-term
block ("[IL3] = the (ITER-LAW-3) theorem, ACCEPTED 2026-08-03: the
display c₃ = z̄^{δ₃}·z₂^{D₂}·z₁^{D₁} (δ₃ = ⌊(s₃+s₃′)/e₂⌋; D₂ =
(s₂-defect + ℓ₁γ₃δ₃)/e₁; Σ = D₂γ₂ + δ₃γ₃(ℓ₁′−ℓ₁w₁Φ₁); D₁ = (s₁-defect
+ ℓ₀Σ)/e₀) PROVED on the 3-read standard-lift harness class OFF the DCX
corner {g₀ = g₁ = 1, δ₁ = 1, s₂(γ) = s₂(γ′) = e₁−1, S₁+s(γ₂) ≥ 2e₀}
(EMPTY at e₀ ≤ 2) — RUNG n = 2 of (ITER-LAW-n). RESIDUALS:
(W-MULT-3-DCX) OPEN (instance-true 132/132); the fenced non-consumed
DEV-1 corner {e₀=1 ∧ d₀≥2 ∧ j≥g₀}; the consumed [IL] base's package
rides through.") at BRIDGE_ADJUDICATIONS:7905–7912 vs the note's S7 r38
bracket.

Consumables read IN FULL or at the cited slices: the target note (all
1,067 lines); ITERLAW3_PROOF (S0 acceptance bracket, S4.0–S4.7 incl.
DIGIT-SPLIT/DEV-1 + erratum + fenced-corner box, CASE-SPLIT, S4.4–S4.6
legs); ITERLAW (theorem display + erratum + L6/L7 rows); L3CONVERGENCE
(S2 Candidate 2 + S3 strategy); ITERLAW4_PROBE (header, F-SUB row,
verdict tail); BRIDGE_ADJUDICATIONS (both acceptance blocks + r38 entry).

— ITERLAWN-PE, round 1 (execution+content), Fable. The acceptance
counter stays 0/2; errata (two display cures + optional token sweep) are
cheap; round 2 should re-run both executables (byte-exactness) and
re-audit only the cured sites plus one fresh content spot-check.
