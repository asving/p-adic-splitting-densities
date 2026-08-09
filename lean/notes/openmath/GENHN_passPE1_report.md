# GENHN passPE1 — first hostile pass (2026-08-09)

**VERDICT: NOT CLEAN — 2 CRITICAL + 1 GAP + 2 MINOR (+4 remarks). The
clean count stays 0/2.** Headline: **LEMMA GENHN-T(b) (tower
composition) is REFUTED at the leaf level by constructed n = 8
counter-instances, PARI-confirmed on two independent oracle routes**
— the note-frame inner read (division in the stage algebra, Φ′ = 0)
predicts composed σ {(4,2)} and {(4,1),(4,1)} where the true fields
give {(8,1)}; the defect's mechanism is identified exactly (the
Φ′-classes of the composed slot basis, which the stage algebra kills,
undercut the stage-algebra pins), and a corrected read (the composed
key Φ₂'s development of f itself) matches PARI on all constructed
instances. Scope: n ≥ 8 towers only — P(5), the n ≤ 7 assembly, the
genre classification, GENHN.C at μ = 2, and GENHN-T(a)'s
event-level criterion all SURVIVE this pass, several now with
first-ever machine contact (the f₁ = 3 stage, the comp = 2 band
census, the F₈-letter refine transfer, the (1,3,2) σ-dictionary).

Target: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` at HEAD
d64b0a8 (850e77e body + [r1] + [e2] errata bc1b996/961d0ff/46bf675/
58b1080). Instrument: `verification/openmath/genhn_pe1_fresh.py`
(independent: no battery imports; own slot-min reader; PARI via
global factor + nfinit([g,[2]]) + idealprimedec — NO factorpadic),
artifact `genhn_pe1_fresh_output.txt`, GREEN as an instrument
(0 violations on its scored checks; the note-frame refutation is
recorded as a 4-instance tally, not an instrument failure).

---

## FINDINGS

### F1 — CRITICAL. LEMMA GENHN-T(b): the tower composition's inner
### read is unsound; composed σ refuted at constructed n = 8 members.

**Claim attacked** (S8, proof of (b)): "The inner opening happens
inside the (μ, K) stage system ... Apply THEOREM GENHN.CLASS +
GENHN.A TO THAT SYSTEM ... σ-dictionaries compose as
(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s). No new mechanism." Consumed by
THEOREM GENHN.B's "(CS-1) and (CS-2) hold ... towers included via
LEMMA GENHN-T" — load-bearing for every n ≥ 8 genre with a decided
inner leaf.

**Counter-instances** (outer genre (2,1,4) at n = 8, q = 2, h = 1 —
the note's own first-live tower geography, same entry shape as the
battery's P8 witness; f(x) = G(x²−2), so the outer stage state IS
G's coefficient tuple; disc ≠ 0 verified on each):

| G(Y) | note-frame inner read (stage algebra) | T(b) composed σ | PARI (both routes) |
|---|---|---|---|
| Y⁴+16Y+96 | pins (21,14), inner-RAM(21) | {(8,1)} | {(8,1)} — agrees, but see below |
| Y⁴+16Y³+32Y²+96 | pins (28,14), residual T²+T+1 irred/F₂ → inner-INERT | **{(4,2)}** | **{(8,1)}** |
| Y⁴+16Y³+32Y²+224 | pins (30,14) → inner-2SIDED(14,16) | **{(4,1),(4,1)}** | **{(8,1)}** |

(+ deep-perturbation variants of each: same refutations; 4 refuted
jobs total. Oracle route 1 = global nfinit/idealprimedec; route 2 =
factorpadic cross-check: each octic is LOCALLY IRREDUCIBLE with
e = 8, f = 1. Base-genre controls validate the verifier's semantics:
plain (2,1,2) INERT/2SIDED/RAM constructions give {(2,2)} /
{(2,1),(2,1)} / {(4,1)} exactly as GENH4's accepted dictionary.)

**The mechanism (exact, not a conjecture).** The composed coordinate
ring has FOUR slot classes per dv₂ = 4v ladder: {1, x, Φ′, xΦ′} at
classes {0, 2, 1, 3} mod 4 (x² = Φ′ + 2, x³ = xΦ′ + 2x). The note's
inner read develops the stage polynomial G(Y) over the stage ring
R = Ô[x]/(Φ′) — where Φ′ ≡ 0 — so it sees only the {1, x}-shadow.
But at an actual root x₀ of f, Φ′(x₀) = Y₀ ≠ 0 (dv₂(Y₀) = 5 here):
the R[Y]-division identity lifts to Ô[x][Y] only modulo
Φ′·H(x, Y), and evaluation injects the correction Y₀·H at dv₂ =
5 + dv₂(H). Concretely, the honest inner object — the development of
f ITSELF by the composed degree-4 key Φ₂ := Φ′² − 4x (division in
ℤ[x], no quotient) — carries Φ′-class terms the stage algebra
killed: for the second row, C₀ = 128 + 128x + **16Φ′** + 64xΦ′, and
16Φ′ sits at dv₂ = 21, UNDERCUTTING the stage-algebra pin u₂ = 28.
True pins (21, 14) → inner-RAM(21) → v(Φ₂(x₀)) = 21/8 → 8 | e →
{(8,1)} = PARI, on 3/3 instances (verified in the instrument:
`inner_read_true`, scored 6/6 jobs). Even the first row, where σ
agreed, has its LEAF LABEL wrong: stage-algebra RAM(21) vs true
RAM(25) (C₀ = 128 + 32Φ′; the 32Φ′ is the carry from 16x² = 32 +
16Φ′) — so tower COUNT laws priced through T(b) are also wrong, the
agreement was parity luck.

**What survives / what breaks.** GENHN-T(a) — the criterion (towers
⟺ μ ≥ 4 ⟺ n ≥ 8) and the EVENT-level witness — survives: in each
instance and in the battery's P8 witness the inner CS event's entry
data (hull (0,10)–(4,0), residual (y+1)²) sits strictly below the
correction floor (entry pins dv₂ ≤ 20 < 21), and the corrections are
key-term products landing strictly above the side. What breaks:
GENHN-T(b)'s proof AND its leaf-level content; S8(b)'s grade line
("inherits GENHN.A's clause grades at each level"); THEOREM GENHN.B's
tower clause, hence the display "P(n) for ALL n ... conditional
EXACTLY on {[GENHN-HE(μ ≥ 3)]} ∪ {S9 boxes} ∪ {arc stack}" — the word
EXACTLY is now false for n ≥ 8: an unlisted defect exists. P(5)/P(6)/
P(7) and the μ = 2 σ-theorem GENHN.C are tower-free and untouched.
The battery could not catch this: GENHN-BOX-3 honestly disclosed
"tower LAWS (witness only)".

**Failure scenario.** Any degree-≥ 8 density assembly that prices a
tower genre through T(b) at a decided inner leaf emits wrong σ
strata — e.g. it books an unramified-quadratic residue extension
{(4,2)} on a locus whose members are totally ramified octics
{(8,1)}; Σ_τ R_τ = 1 would silently misdistribute mass between τ's
at n = 8.

**Repair direction (from the data, not prescribed).** The corrected
inner state = the Φ₂-adic development of f in the composed slot
basis — i.e. genuine order-2 OM types (composed keys), which is
exactly the machinery the repo's classifier already implements at
Lean level. The multiplicative (e,f)-ladder/census composition ITSELF
may well survive under that frame (my corrected reads compose
multiplicatively and match PARI); what cannot survive is "no new
mechanism: this is GENHN.A applied to the stage system" — the stage
algebra is not evaluation-faithful at inner-leaf depth.

### F2 — CRITICAL (display-scope; count content rescued elsewhere).
### LEMMA GENHN-1's per-coordinate budget display is false at each
### genre checked, including the battery's own f₁ = 1 rows.

The displayed budget (S3.2, inside the lemma box, graded PROVED):

    v(a_{j,i}) ≥ ⌈(μ−j)h + (e₁ − i)h/e₁⌉⁺

exceeds the true on-side floor ⌈((μ−j)D′ − i)h/e₁⌉ (+1 at pinned
lattice slots) by h at every slot — the correct base is the side
height at abscissa jD′ + i, not (μ−j)h + (e₁−i)h/e₁. Instances (all
internal to the note + its own sealed runner):
* E3 = (2,1,3), h=1: displayed floors (4,4,3,3,2,2), total 18; the
  note's OWN S2 list "(3h, (5h+1)/2, 2h, (3h+1)/2, h, (h+1)/2)" +
  3 pins gives (4,3,3,2,2,1), total 15 = the exponent in the
  battery-verified volume (E3(1) = 512 = 2^{6·4−15}, P6 EXACT).
* E31 = (3,1,2), h=1: displayed total 15 vs true 11 (battery:
  8,192 = 2^{24−11}, P5 EXACT). The sealed runner's own gen_E31/
  gen_E3 constructions use ceil_div((6−i)h,e₁)-style TRUE floors,
  not the display.
* GENH4's E genre (2,1,2): displayed total 10 vs law_E's 8
  (law_E(2,5,1) = 4,096 = 2^{4·5−8}).
With the displayed floors, the lemma's own clause "total = the entry
exponent (no over/undercount)" is violated at each of these genres —
the display contradicts the statement it sits in. This is BEYOND
GENHN-ERR-1's declared residue (which scopes the S-vs-D′h worry to
f₁ ≥ 2 count displays): the budget display is false at f₁ = 1 too,
at every non-lattice slot (and at lattice slots for h ≥ 2, where the
pin bookkeeping +1 ≠ +h). The [r1] erratum corrected the NODE line
of the same lemma but not this line. Failure scenario: any consumer
that transcribes GENHN-1's displayed floors (a future f-first count
unit, GENH5-DENS mechanics, or a Lean statement fan-out) inherits
entry volumes wrong by factors like q³ (E3) — against a battery that
would then contradict it. Cure: one display correction, no count or
σ movement (S2, the laws, and the runner already use the truth).

### F3 — GAP. The [e2]-E1 band-trichotomy transport to f₁ ≥ 3 is
### claimed without derivation (and E2's readability parenthetical
### fails at the deeper band heights); machine-adjudicated TRUE at
### the first-live instance by this pass's fresh legs.

E1's corrected sentence claims "at the μ = 2, f₁ ≥ 2 genre the band
read follows exactly this r3 trichotomy", citing GENH4-CAP(F) at
(e₁,f₁) = (1,2) — a genre whose band is ONE height deep (comp = 1).
At (1,3,2) (= E13(1), first live n = 6) the band is TWO heights deep:
comp(N) = 2, comp(N+1) = 1, and the deeper height is value-UNSTABLE
(an out-of-window class-0 digit at height N undercuts any computed
value N+1) — so E2's parenthetical "at band heights ... (the value
is [readable]; the full K-residue is not)" is false at the deeper
band heights for f₁ ≥ 3, and the trichotomy's transport needs the
η-independence argument (a nonzero readable slot part cannot be
killed by the unread component) plus the undercut analysis — neither
displayed; the "beyond it" exclusion list (μ ≥ 3, or e₁ ≥ 2 mixed)
does not cover μ = 2, e₁ = 1, f₁ ≥ 3, so the genre sits in the
claim's scope with only a (1,2)-shaped authority. ADJUDICATION BY
MACHINE (this pass, FR-A/FR-B): at (1,3,2)/q=2 the trichotomy AND
the Q^{comp}−1 census hold exactly — exhaustive sweeps N = 7
(32,768 states: RAM(7) = 3·2¹³ band-censused, UND = 2¹³) and N = 8
(2,097,152 states: RAM(7) = 7·2¹⁸ full |K|−1-censused, UND = 2¹⁸),
plus 36/36 band-RAM PARI jobs at {(2,3)} including out-of-window
perturbations. So: TRUE at the tested instance, UNPROVEN in the
text — a justification gap, not an error.

### F4 — MINOR. S7 stage-RAM display: "v(Y) = u/(2e₁) with u odd ⟹
2e₁ | e(L)" silently needs (T1) when gcd(u, e₁) > 1 (e.g. e₁ = 3,
u = 9: u/(2e₁) = 3/2 alone gives only 2 | e(L); with (T1)'s 3 | e(L)
the value-group argument gives 6). The display attaches "(with (T2))"
to the degree count but nothing to this step. One line.

### F5 — MINOR. S12 P9 reports the V p=2 diagnostic tail as
1,216 jobs / 349 mismatches; S11.E's run-2 paragraph says the same
tail was 1,216 / 350. The isolated re-run (this pass) reproduces 349
deterministically; the 350 is run 2's tally with the 4 gp
precision-misses scored as Nones (1 of the 4 was a tail job). The
two numbers sit 30 lines apart with no reconciliation sentence.

## REMARKS (no grade)

* R1 (charge note): the dispatch's fresh-route suggestion "a 3-stage
  tower at n = 8 or 12" is unconstructible by the note's own T(a)
  arithmetic (3 stages need μ₁ ≥ e₂f₂μ₂ ≥ 2·4 = 8, hence
  n ≥ e₁f₁μ₁ ≥ 16); this pass tested the 2-stage LEAF level instead
  — where the composition already fails (F1).
* R2 ([e2]-E3 verified CLEAN): the L/O_L forcing chain checks at
  both witness patterns — x² + 2x + 4 over ℤ₂: one slope-1 side,
  residual y²+y+1, e = 1, f = 2, θ = 2ω with R = ℤ₂[2ω] index-2
  non-maximal, R/2R ≅ F₂[ε]/(ε²); x² − 8 (h = 3): e = 2, f = 1,
  m_R = (2, θ) non-principal. Display-scope confirmed: the fresh
  legs' counts/σ never consume R's ring structure.
* R3 ([e2]-E2's derivation verified): comp(m) = #(in-window
  F_Q-components of the height-m slot) re-derived from GENHN-2
  (within-class components at O-heights v_t = v₀ − th; independence
  of {1, η, ..., η^{f₁−1}} makes a nonzero readable part unkillable
  by the unread component — whence the census counts readable data
  only). First machine contact at comp = 2 delivered GREEN (F3).
* R4 (instrument note): GN-TOWER's "min-n scan" hard-codes the range
  μ ∈ [4, 8] — it verifies the arithmetic minimum, not the μ ≥ 4
  criterion itself; the criterion's real tooth is the zero-stage-CS
  census on the μ ≤ 3 rows, which is present. No action needed.

## CLEAN CHARGES (attacked and held)

1. **[e2]-E2 census clause** — derivation re-run from the slot
   model; general form + honesty scoping accurate; FIRST f₁ ≥ 2 and
   FIRST comp = 2 machine contact both EXACT (FR-A teeth prove the
   census is load-bearing: swapped censuses 7·2¹³ / 3·2¹⁸ refused).
2. **[e2]-E3 carrier erratum** — forcing chain + witnesses verified
   (R2); ridered-site list spot-checked (GENHN.A(i), S3.1, S6.1
   gr-reaim) — coherent.
3. **GENHN.A(iv) at f₁ ≥ 2** — the refine transfer holds pointwise
   at (1,3,2), κ = 4, all 7 letters s ∈ F₈^× × 3 A₁-variants × 2
   tails (42 exact re-divisions: both pins die into the floored node
   {dv(A₀) > 8, dv(A₁) > 4}); 7/7 wrong-letter controls leave the
   pin alive at 8 — the binomial kill R(T+s) = T² is real with
   genuine K = F₈ lifts ŝ = s₀ + s₁(x/2) + s₂(x/2)² (times n(4)).
   First f₁ ≥ 2 refine-transfer machine contact.
4. **GENHN.A(v) re-based law at f₁ = 3** — the (μ=2, F₈) cluster
   read on dv = v with the [r1]-corrected node (dv(A₀) ≥ 7 = D′h+1,
   NOT the S-node 3) reproduces both exhaustive partitions exactly;
   the [r1] node correction independently confirmed at this instance
   (the pre-r1 S-node would put (0,3) below the side).
5. **GENHN.C at a fresh genre** — the (1,3,2) dictionary
   {(2,3)} / {(1,3),(1,3)} / {(1,6)}, called "visibility-floored, no
   row" by S7: PARI-confirmed on constructed INERT (both T²+T+1 and
   T² + ηT + η² — genuine η-letters), SPLITEQ (roots 1, η), 2SIDED
   (4,5), deep RAM(9), each + deep perturbation; band-RAM(7)
   lift-stability 36/36 (η-independence physical). UND tail
   genuinely mixed ({(2,3)}×6, {(1,3),(1,3)}×5, {(1,6)}×1) —
   conservative drain honest.
6. **GENHN.CLASS + realizability floors** — datum/finiteness/
   uniformity walked; μ = 2 exhausts n = 4, 5 (products 4 or ≥ 6);
   E3/E31 entry lists + volumes re-derived by hand and they, not
   GENHN-1's display, are what the battery verified (see F2).
7. **S6.2 bracket reconciliation** — (|K|−1)|K|^{2κ−1} =
   |K|^κ·(|K|−1)|K|^{κ−1}; macroscopic rate |K|^{e₁·(c(μ)+1)Δ} =
   q^{2e₁f₁Δ} at μ = 2 = GENH4's q^{e₁f₁Δμ}: arithmetic checks.
8. **P8/GN-TOWER witness (charge 4)** — frame ('EMB',8,(0,8),2,1,4,1)
   at q = 3, stage dvs (10,None,5,None), hull (0,10)–(4,0), residual
   (T−1)² with the j = 2 lattice pin nonzero in char 3: consistent;
   the witness fires the EVENT only, which F1's mechanism leaves
   intact (entry pins below the correction floor).

## MACHINE LEG (sealed battery integrity)

* Pins: 7/7 md5 match (runner-as-run 637427dc…, artifacts
  dd9edbea… / 7d4a3e86…, five supplier pins per S11.A).
* Isolated re-run (fresh dir, full import closure — NOTE: the
  runner's import closure spans ~23 local modules beyond the 7
  pinned files; only the pinned 7 are integrity-checked by GN-PIN):
  **GREEN, 2,223,050 checks / 0 violations, teeth 2/2/2/2/1, 450.3s**;
  results JSON content-identical to the committed artifact except
  `elapsed_s` (450.3 vs 450.0); oracle rows identical including the
  1,216/349 diagnostic tail — deterministic reproduction.
* Tautology audit: law legs compare enumerated-and-READ observations
  (gen_* constructions → read_* readers) against separately coded
  law formulas; cmp_tab is two-sided (obs ∪ exp keyset); the five
  teeth mutate laws/grammar/floors and demand disagreement; GN-SIGMA
  scores PARI answers against the note's dictionary with the
  certified-perimeter gate as disclosed. The E31/E3 constructions
  use the TRUE entry floors (S2's), decorrelating the machine leg
  from the false GENHN-1 display (F2) — the battery is sound, the
  display is not.

## FRESH ROUTE (disjoint from the sealed battery's coverage)

First f₁ ≥ 2 stage rows ever (battery: all rows f₁ = 1): (1,3,2)
exhaustive sweeps at (q,N) = (2,7) and (2,8) [FR-A]; first comp = 2
band census; first F₈-letter refine transport [FR-C]; first (1,3,2)
σ contact incl. η-flavored INERT [FR-B]; first tower σ legs at all
(battery: witness only) — which produced the F1 refutation plus the
corrected-read cross-validation [FR-D]. Oracle decorrelation: global
nfinit/idealprimedec, no factorpadic in the scoring path; controls
at (2,1,2) reproduce GENH4's accepted dictionary 3/3.

## GRADE LINE

**passPE1 = NOT CLEAN: CRITICAL ×2 (F1 GENHN-T(b) tower-leaf
composition, refuted with counter-instances; F2 GENHN-1 budget
display, false at each checked genre incl. f₁ = 1), GAP ×1 (F3
E1/E2 f₁ ≥ 3 band transport — machine-adjudicated true at first-live
instance, underived in text), MINOR ×2 (F4 S7 RAM display's silent
(T1); F5 349-vs-350 tail tally). Clean count 0/2 → stays 0/2.**
Repair scope by clause: (F1) S8(b) + GENHN.B tower clause + the
"EXACTLY" conditionality display + a new named S9 item (the
composed-key inner frame); (F2) one display line in GENHN-1 (+ its
node-computation remark); (F3) either derive the f₁ ≥ 3 band
adjudication (the η-independence + undercut argument is short and
this pass's legs witness it) or rescope E1's sentence to (1,2);
(F4)/(F5) one-liners. Consumers to notify at repair: GENIND
(accepted; consumes GENHN.B's (CS-1)/(CS-2) — its n ≥ 8 instances
inherit F1's conditionality), the S9.2 endgame list, and
PROJECT_STATE's uniformity display. n ≤ 7 content — including P(5)
— is not touched by any finding of this pass.
