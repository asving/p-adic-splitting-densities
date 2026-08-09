# HE7 passPE3 — hostile verification report (THE ACCEPTANCE ATTEMPT; fresh context, zero prior stake)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 1 MINOR (+1 remark). Nothing at
GAP-or-worse survived my verification attempts. The three r3 minor repairs
are correct and damaged nothing. Machine leg: all pins byte-identical
worktree = HEAD = r3 e0c0240 = r2 = seal; isolated /tmp re-run of the
FULL sealed battery + both supp legs GREEN (1,587 members, 0 violations,
6/6 teeth; results-JSON leaf-diff vs committed = timing only); the r3
λ₂-histogram disclosure independently reproduced by regeneration
({11: 38, 12: 1, 15: 3}, 42 total, all chains one-step). Fresh route
GREEN, TWO legs, both sealed-then-run: (1) a constructed f₁ = 2 / e₁ = 1
family — the LAST never-machine-exercised σ-genre HE7-BOX-2 names — 780
members, σ == PARI 780/780, 0 violations; (2) a constructed μ₂ = 3
(n = 12) refine probe at the one seam this pass found — 144/144 PARI on
96 mixed-residual nodes, the first machine contact of ANY refine at
μ₂ ≥ 3. Per HE7-BOX-1 [r3] the 2-clean count completes: **1/2 → 2/2 —
HE7 IS ACCEPTED. The text freezes; dated appends only.**

Target: `lean/notes/openmath/HE7_PROOF_2026-08-08.md` at HEAD (r3
e0c0240; arc seal 1956151 → verdict 4c42f9d → r1 aafb481/d58680e/2970615
→ PE1 5c98481/7b66364 → r2 83ced80/1811605 → PE2 235cc22/8f5f2a6 (CLEAN,
count 0/2 → 1/2) → r3 e0c0240). Prior reports `HE7_passPE1_report.md`
and `HE7_passPE2_report.md` read first; their routes not re-walked.
Protocol: quote-and-classify, fix nothing.

Attack order executed: (1) the three r3 repairs verified AS MATHEMATICS
(F-1's W ≠ 0 discharge including the HE7-12(d)/HE7-13 joint-induction
well-foundedness; F-2's pigeonhole; F-3's histogram recounted from
regenerated members) and the full r3 diff audited for collateral damage
(60 insertions, 2 reflow deletions — exactly the four disclosed blocks).
(2) The never-owned surfaces: §S3 (SLOT₂) residue arithmetic re-derived
at d_r ≥ 2; §S8 dictionary rows 1–4 re-derived + the exhaustiveness of
the six-row table at μ₂ = 2; THEOREM HE7.A's (1)(2)(3) assembly walked
clause-by-clause against §S5.7/§S5.8/§S7; COROLLARY HE7.B(i)'s scope
sentence checked verbatim against COROLLARY HE6.B [r1] (read at source)
and HE6R1_RECON §S3.2/§S3.4 (LEMMA HE6R1-2 read at source). (3) Machine
integrity: md5 pins across five arc commits, isolated re-run, instrument
spot-audits. (4) Fresh routes (below). The one finding came out of
attack (2), and its downstream mathematics was then machine-verified by
fresh-route leg 2.

---

## FINDINGS

### F-1 [MINOR] THEOREM HE7.A(3)'s α-refine wiring cites LEMMAS HE7-13 /
### HE7-8 at nodes their hypotheses exclude: a MIXED residual (repeated
### factor PLUS a distinct factor at one slope) — first live at μ₂ = 3,
### n = 12, inside COROLLARY HE7.B(i)'s region; vacuous at every
### machine-certified degree

**Location:** THEOREM HE7.A(3) (§S2, the [r2] bracket); LEMMA HE7-13's
hypothesis (§S5.8); LEMMA HE7-8's hypothesis (§S7); §S6 [r1](iii).

**Quote (HE7.A(3) [r2]):** "the strict slope increase λ₂^{(0)} <
λ₂^{(1)} < ⋯ that LEMMA HE7-8 consumes is **LEMMA HE7-13**, derived, not
assumed". **Quote (HE7-13's hypothesis):** "suppose the polygon of f_S
with respect to Ψ̃ is the single side of integer slope λ₂ > T₂ with
residual R₂ = (Z − s₂)^{μ₂}". **Quote (§S6(iii)):** "*Several distinct
repeated factors at one node.* Then the classification above is applied
per distinct factor, each with its own block, by LEMMA HE6R1-2".

**The defect.** HE7.A(3) fires the α-refine "at a slope λ₂ = u₂/ℓ₂ whose
residual R_{λ₂} has a repeated irreducible factor r₂ of multiplicity
m₂ ≥ 2 … ℓ₂·deg r₂ = 1" — this includes residuals like
R₂ = (Z − a)²(Z − b), b ≠ a (repeated PLUS simple at ONE slope), and
side-with-repeat plus OTHER sides. There the cited lemmas do not apply:
HE7-13 requires the PURE power (Z − s₂)^{μ₂} on a single side, and
HE7-8's chain hypothesis is likewise "each step at a node whose polygon
is the single side of length μ₂ with residual (Z − s_j)^{μ₂}". §S6(iii)'s
per-block sentence — the note's mechanism for multi-factor nodes — names
only "several distinct REPEATED factors", not a repeated factor mixed
with simple ones, and in any case defers to level-i restatements of
HE6R1-2 that the note explicitly does NOT display ("The level-i
restatements of HE6R1-1/2/3 are not separately displayed here … they
inherit HE7-BOX-1's grade"). LEMMA HE6R1-2 at source (HE6R1_RECON §S3.4)
is level-1 block projection only.

**Moreover HE7-13's conclusion-as-stated is genuinely FALSE at mixed
nodes** — the hypothesis is load-bearing, not decorative. Constructed
counter-instance (fresh-route leg 2, member (p, u, s, λ₂) = (5, 5, 1, 11),
R₂ = (Z−1)²(Z−2), pins (0,33),(1,23),(2,11),(3,0)): after the refine at
s₂ = 1 the polygon of f wrt Ψ − w is (0,34),(2,11),(3,0) — **the λ₂ = 11
side survives** (it now carries the b = 2 class with SEPARABLE linear
residual; PARI: σ = {(4,1),(8,1)}, the (4,1) factor = the undisturbed
b-class). So "every slope of the polygon … is > λ₂" fails at mixed
nodes, and no repair can simply relax HE7-13's hypothesis: the correct
continuation is per-class (the refined class's roots move strictly up by
the residue match — HE7-13's own proof mechanics, which are per-root —
while every other class's dv₂ and residue at λ₂ are UNCHANGED because
w's residue ι(s₂) ≠ their β₂-residues; the slope-λ₂ side re-appears with
the repeated factor REMOVED, separable, decided by HE7.A(2) at the
refined key via LEMMA HE7-12(c); the slopes the chain refines AT still
strictly increase; termination by ≤ μ₂ separation steps + pure tails,
the same bookkeeping as the [r3] peel pigeonhole).

**Why MINOR and not GAP (the PE2 F-2 precedent, same defect shape).**
(a) Vacuous at every machine-certified degree: at μ₂ = 2 the repeated
factor uses the whole residual degree, so every mixed configuration
needs μ₂ ≥ 3, i.e. μ ≥ 6, n ≥ 12 — no sealed or supp member reaches it
(all 42 + 156 + 78 observed refines are pure). (b) The exposure is
COROLLARY HE7.B(i)'s n = 12–15 sub-region, a composition claim at arc
grade with no machine certificate, and §S6(iii) already discloses that
the multi-factor-node mechanism is a non-displayed graded transfer.
(c) The conclusion VERIFIED downstream at the exact configuration:
fresh-route leg 2 constructed 96 mixed nodes (plus 48 pure μ₂ = 3
nodes) and the derived per-class continuation decides σ with **144/144
PARI agreements, 0 violations** — including 2-step chains and the
strict increase of refined-at slopes. (d) The repair is in-toolkit: one
§S6(iii) phrase extension ("repeated or not" / mixed residuals) plus a
HE7-13 rider stating the per-class version, or equivalently THEOREM
HE7.C's tree bookkeeping (a mixed refine strictly splits off decided
mass). Failure scenario (of the text, not the math): a reader granting
only displayed lemmas cannot justify the read's continuation at an
n = 12 member with R₂ = (Z−a)²(Z−b); with the naive reading of §S8's
"lands at a strictly larger slope" transplanted to μ₂ = 3 they would
even predict a false polygon. No certified claim moves.

---

## REMARK (not a finding)

* **R-a.** THEOREM HE7.A(2) + (3) jointly leave the same mixed-residual
  configuration formally uncovered one clause earlier: a SIMPLE factor
  r₂′ of an inseparable R_{λ₂} is decided by neither (2) (whole-residual
  separability hypothesis) nor (3) (which speaks only of the repeated
  factor). Same first-live point (μ₂ = 3), same §S6(iii) block-transfer
  route, same downstream verification (leg 2's b-classes all decided
  correctly) — folded into F-1 rather than counted separately.

---

## CLEAN CHARGES (attacked and survived)

1. **r3 F-1 (W ≠ 0 at HE7-12(d)) — verified as mathematics.** The
   joint induction is well-founded: base W = w₁ a single nonzero
   (LIFT₂) polynomial; at step j, HE7-13's applications at steps < j
   give pairwise-distinct dv₂(w_i), and the ultrametric-equality-at-a-
   unique-min argument is exact — I re-derived it two levels down
   (dv₂(A + B) = dv₂(A) when dv₂(A) < dv₂(B): at A's attaining slot s*,
   ℓ·dv(b_{s*}) + s*u ≥ dv₂(B) > dv₂(A) forces dv(a_{s*} + b_{s*}) =
   dv(a_{s*}) by the same argument on level-1 monomials, where
   coefficientwise v is a genuine valuation) — so dv₂(W) = λ₂^{(0)} < ∞
   exactly and W ≠ 0. No circularity: HE7-12(d) at step j consumes
   HE7-13 at steps < j only. The W = 0 fallback sentence matches
   HE7-13's "W = 0 or as in LEMMA HE7-12(d)" split verbatim.
2. **r3 F-2 (the mid-chain-peel pigeonhole) — verified.** Each peel
   drops μ₂ by exactly 1 (LEMMA HE6R1-3 peels one simple factor) and
   μ₂ = 1 is decided, so ≤ μ₂ − 1 peels; an infinite chain has an
   infinite constant-μ₂ tail on a fixed f_S^{(seg)} | f_S, separable
   (factor of separable f, disc ≠ 0), starting key Ψ − W covered by
   HE7-12(d) — HE7-8's argument applies verbatim to the tail. The
   μ₂ = 2 vacuity sentence is consistent with the artifacts (42
   refine firings, all one-step — reconfirmed from the frozen JSON and
   by my regeneration).
3. **r3 F-3 (the δ = ∞ coverage disclosure) — INDEPENDENTLY RECOUNTED.**
   My own regeneration of the 42 refine members from the sealed
   enumeration gives λ₂ histogram **{11: 38, 12: 1, 15: 3}** and
   chain-length histogram {1: 42} — the r3 sentence ("11 × 38, 12 × 1,
   15 × 3; the one λ₂ = 12 member exercises it") is exact, and the
   parity mechanism (Φ′ | w iff s₀ = 1 iff λ₂ odd at u odd, ℓ = 2) is
   correct. The R-a/R-b dispositions accurately describe the frozen
   code paths.
4. **r3 collateral-damage audit.** The full diff 8f5f2a6 → e0c0240 on
   the note is exactly the four blocks the commit message names
   (HE7-12(d) [r3] rider; HE7-8 [r3] box; §S9 BOX-1 [r3] paragraph;
   §S11 [r3] disclosures + the B2 cross-reference line). No statement,
   frozen number, or sealed artifact moved (md5s verified below); the
   BOX-1 count-holds rationale matches the ledgered HMENU3-ANNEX-A
   precedent (fold commit b3c05be).
5. **§S3 (SLOT₂) re-derived at d_r ≥ 2** (never owned end-to-end):
   (S3.1) exactness from GENHN-2 at (T1)/(T2) points; class separation
   = gcd(u, ℓ) = 1 via s ↦ su bijection mod ℓ (attaining slots share
   value k, and value ≡ su mod ℓ pins ONE class — clause (a) exact);
   the (S3.2) bracket algebra checked (exponent bookkeeping
   ϖ^{m₀} = ϖ^{m₀−tu}ϖ^{tu} exact); γ_t ≠ 0 exactly at attaining t;
   the K-basis argument (r irreducible of degree d_r ⟹ {β^t} a K-basis
   ⟹ Σγ_tβ^t ≠ 0 ⟹ ι^{(2)}-image ≠ 0) is complete; cross-class terms
   sit strictly above k (≢ k mod ℓ and ≥ min). Clause (c) is the
   ultrametric applied twice, no exactness claimed. My leg-1 members
   exercise the dual pattern (the level-1 f₁ = 2 within-class basis
   feeding K = F_{p²} residues) — 780/780.
6. **§S8 dictionary rows 1–4 + exhaustiveness** (never owned): row 1
   (λ₂ ∉ ℤ ⟹ ℓ₂ = 2, deg R₂ = 1, class 8 = deg f, e = 8, f = 1); rows
   2–3 (ℓ₂ = 1, R₂ quadratic inert/split, class sizes 8 / 4+4, (4,2) /
   (4,1)²); row 4 (two length-1 sides force ℓ₂ = 1 and linear separable
   residuals, (4,1)²). Exhaustiveness at μ₂ = 2: polygon length 2 =
   one side (ℓ₂ ∈ {1,2}; at ℓ₂ = 1 deg R₂ = 2: inert / split /
   (Z−s₂)² → row 5) or two sides → row 4, plus Ψ | f → row 6; a
   repeated non-linear or ℓ₂ ≥ 2 repeated configuration is
   degree-impossible at μ₂ = 2. Complete.
7. **THEOREM HE7.A's assembly**: (1) = HE7-9(a) + Σn_{λ₂} = deg f_S
   with n = D″L; (2) = the §S5.7 sandwich (nonemptiness + Galois
   stability + local forcing ≥, sum = forces =, single orbits, e·f
   splits); (3)'s three branches: α-refine (exists by (LIFT₂) at
   λ₂ > T₂ via §S4.3's chain; licensed at the refined key by HE7-12;
   finite by HE7-8 + HE7-13 — the pure-node case; the mixed-node
   sub-case is F-1); level-3 (THEOREM HE7.D) gated by μ₂ ≥ 4 via
   L ≥ m₂(ℓ₂ deg r₂) ≥ 4 and clause (1) — display exact, floors [r2]
   correct; the pre-r1 error paragraph accurate. The §S6 induction's
   level-2 instances re-checked: bound₂ = (L₁−1)u₁ + ℓ₁bound₁ =
   (ℓd_r−1)u + ℓ(D′−1)h = (‡₂) exactly; the (S6.3) cascade at j = 1
   matches §S5.3 exactly (ρ₁ = ℓ[(λ−T₁) + ε₀] both routes).
8. **COROLLARY HE7.B(i)'s scope vs COROLLARY HE6.B [r1] + HE6R1's
   reconciliation scope** (never owned): HE6.B [r1] read at source —
   its exclusion is exactly "a side carrying a repeated irreducible r
   with ℓ·deg r ≥ 2"; HE7.B(i) removes it at n ≤ 15 via μ ≤ ⌊n/D′⌋ ≤ 7
   (D′ ≥ 2 at any composite stage, all stages of an n ≤ 15 history
   included), μ₂ ≤ ⌊7/2⌋ = 3, and the μ₂ ≤ 3 non-propagation; the
   ℓ = 1 branch citation ("HE6R1_RECON §S3.2, ten items") matches the
   source's verdict sentence verbatim; the proper-block first-bite
   μ ≥ 5 / n ≥ 10 claim consistent with HE6R1-2's statement and inside
   the clause's region as claimed. The (i)/(ii) conditionality split
   (composition at arc grade, §S9) honest — with F-1's caveat that the
   mixed-node display also sits in (i)'s n = 12–15 sub-region.
9. **The §S1 CONVENTION + peel at r3-HEAD**: unchanged by r3; the
   at-most-once-per-key reading and the μ₂ − 1 shift verified
   consistent with the [r3] pigeonhole (which correctly allows one
   peel per ITERATE across a chain).
10. **HE7-BOX-2's coverage sentence at r3-HEAD**: still accurate — and
    my leg 1 partially discharges its last named σ-hole (f₁ ≥ 2 stage
    genres; char 0, everything-block, disclosed), while leg 2 gives
    μ₂ = 3 refines their first exercise (BOX-5's μ₂ ≥ 3 realm; peel at
    a PROPER block remains proof-only, as the box says).

---

## MACHINE LEG (integrity)

* **Pins.** `he7_checks.py` md5 688adbe88447… byte-identical at
  worktree = HEAD = r3 e0c0240 = r2 83ced80 = leg 1811605 = seal
  1956151 = verdict 4c42f9d; `he7r2_supp.py` 71bb6202f72c… identical
  r2 → HEAD; artifacts b2d095a2556a… / f5bedab2ecda… /
  1e787536254c… / f45b5ab1e3b5… and `he7r1_supp.py` 24ece42e4538… all
  match §S11's displayed pins. The r3 commit touched ONLY the note.
* **Isolated re-run** (`/tmp/he7_pe3_sandbox`, full import closure,
  committed artifacts untouched): sealed battery GREEN exit 0, 191.7 s,
  1,587 members, 0 violations, 6/6 teeth fired, results-JSON leaf-diff
  vs committed = {secs} only; `he7r1_supp.py` GREEN 0 violations
  (leaf-diff = the he7_checks_results pin hash, which follows from the
  regenerated JSON's timing leaf — expected in-sandbox artifact);
  `he7r2_supp.py` GREEN 0 violations, leaf-diff = {secs} + same pin
  hash.
* **Instrument spot-audit.** The r3 disclosures checked against the
  frozen code: B2's `a_w < BIG` guard is as described; the B3 peel-guard
  and B1 coupling dispositions accurate. The λ₂ recount (above) is my
  own code against the sealed enumeration — not a re-read of any
  committed number.

## FRESH ROUTE (disclosed; differs from ALL SIX prior routes)

Prior: (a) sealed 1,587-member battery ((2,1,1), d_r = 1); (b) HE6R1's
682 (ℓ = 1, d_r = 2); (c) r1's 8-member peel supp; (d) PE1's n = 12
μ₂ = 3 peel family (refines skipped); (e) r2's 42-member slot leg;
(f) PE2's d_r = 2 α-refine family + polytope leg. **This pass ran two
new legs.**

**Leg 1 — `verification/openmath/he7_pe3_fresh.py` (sealed pre-run at
d912473 with preregistered P1–P6 and a disclosed 2-member smoke;
artifacts at beb5929): a constructed f₁ = 2 / e₁ = 1 family — the first
UNRAMIFIED level-1 σ leg anywhere in the program.** Frame: Φ′ = x² − 2p²
(inert quadratic point, K = F_{p²}, ϖ = p, h = 1), ℓ = 2, d_r = 1,
u ∈ {5,7}, p ∈ {3,5}; r = Z − s with s ranging over F_{p²}^× INCLUDING
proper-extension residues (580 of 780 members) — the level-1 boxed
residual (Z − s)² with s ∉ F_p, reachable by no prior leg; the S1
cocycle twist now multiplies by an element of F_{p²}. Independent
instrument (no he6/he7 import; own exact ℤ[x] arithmetic; cypari2
global-factor + nfinit + idealprimedec oracle, precision-free).
**Result: 780 members (six genres × 2 seeds; zero discards), σ == PARI
780/780, 0 violations; letter alphabet exactly {(4,2)} × 300 /
{(2,2),(2,2)} × 318 / {(2,4)} × 162 (e from level 2, f from level 1 —
the transposed decomposition); 156 refines (slot geometry + strict
increase all green), 78 peels; TEETH: dropping the twist flips 155
predictions and PARI refutes ALL 155 while the twisted read stays
780/780; the lazy dictionary is refuted on 150/150.** Disclosures: the
pre-seal smoke found and fixed a real quotient-misalignment bug in my
`pdivmod`; post-seal, a crash bug in the frame CHECK (slots2 called on
deg-4 Ψ with 2 slots) was repaired with one disclosed line, and a
10-member timing probe at (5,7,(2,3)) ran before the battery (both
post-seal events touched no prediction).

**Leg 2 — `verification/openmath/he7_pe3_probe12.py` (artifacts at
b574f25): the F-1 seam probed at n = 12, μ₂ = 3, sealed frame
(2,1,1).** 144 constructed single-side integer-slope cubic-residual
members (96 mixed (Z−a)²(Z−b), 48 pure (Z−a)³), p ∈ {5,7}, s ∈ {1,2},
λ₂ ∈ {11,12}, hand-derived μ₂ = 3 twist exponents. The derived
per-class continuation (top-first refine, separable sides decided at
the current key): **σ == PARI 144/144, 0 violations; refined-at slopes
strictly increase incl. two 2-step chains; the mixed-node
counter-instance to HE7-13's conclusion-as-stated recorded** (the λ₂
side survives the refine, carrying the simple class). First machine
exercise of any μ₂ ≥ 3 refine, of {(12,1)} (an ℓ₂ = 3 side), and of
{(4,1),(4,2)} / {(4,1)}³ letters. Two instrument bugs found and fixed
during the disclosed smoke (the Fr12 m₀ missing ℓ-division; the
unreduced-slope refine guard); both were in MY probe code, not in
anything committed by the note.

## GRADE

0 CRITICAL, 0 GAP. The single MINOR is a statement-scope defect of the
same class the arc has twice graded MINOR (PE2 F-2 precedent):
hypothesis overreach at a configuration vacuous at every
machine-certified degree, with the mathematics verified downstream by
construction at the exact configuration (144/144) and an in-toolkit
repair. The r3 repairs are correct; the machine record is bit-stable;
two genuinely new machine frames corroborate the composed results.
**This pass is CLEAN: per HE7-BOX-1 [r3] the 2-clean count completes,
1/2 → 2/2 — HE7 IS ACCEPTED, the first stage-one note through the
2-clean bar. The note's text freezes: dated appends only.** Owed (as a
dated append, not a text edit): the F-1 mixed-residual rider at
§S6(iii)/HE7-13, which can cite this report's leg 2 as its machine
record.
