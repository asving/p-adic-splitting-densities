# LIFT-CORNER — NR-1 ((ITER-LAW-LIFT) at g₀ = 1 ∧ δ₁ = 1): the lift-ORBIT transport instrument + the shift-descent compose

**Unit:** LIFT-CORNER (NR-1 of ILNRES S1; spec ILNRES S5.1, price M; route =
the W-2 shift-descent covariance + window-calculus tail bookkeeping).
Wallclock 2026-08-04, campaign date 2026-08-08. Genre: sealed-preregistration
numerics (two-commit seal) + a conditional COMPOSE (S4; written only on a
0-violation verdict, per the probe-first discipline). **Grade cap (read
first): everything this unit proves is at attempt grade 0/2 AND capped by its
W-2 consumption (GRTW2_PROOF, itself attempt 0/2, no acceptance arc run).**

**Machine leg:** `verification/openmath/liftcorner_checks.py` (this header +
the runner commit BEFORE any full run; verdict appended in commit 2 from the
artifacts `liftcorner_checks_output.txt` / `liftcorner_checks_results.json`).

**Sources of record:** ILNRES_2026-08-08.md S1 [NR-1] + S5.1 (the spec);
ITERLAWLIFT_CORNER_2026-08-08.md (wave 18: the LAWFUL slice measured
104,404/0; the S7 sketch + its one open step (TAIL-STAB)); ITERLAWN_PROOF
S0.1 (the standard-lift class pin + the verbatim residual propagation rider);
GRTW2_PROOF §3.4 (χ-chain/shift-descent), §5 (clause 3 ψ-transport, W2-OPEN-1).

**FENCES.** No edit to any accepted text (ITERLAW/ITERLAWN/ILNRES bodies,
sealed falsifiers, wave-18 artifacts); committed engines consumed READ-ONLY
(in-memory ledger override only, engine_ext precedent); no Lean change; no
orders-≥3 machine claim (the battery is 2-read); no gr(w₂) claim; nothing
here closes NR-1's ledger entry until this note's own acceptance arc runs.

## S1. The corner orbit and the transport frame (derived; sealed pre-run)

At g₀ = 1: ψ₀ = y + c₀ (c₀ ≠ 0), K₁ = K₀, z₁ = −c₀ a SCALAR. The full monic
lift orbit at the corner (deg = e₀d₀, w₁ = e₀h₀, nonzero order-1 residual):
Φ′ = Φ₀^{e₀} + Σ_{k<e₀} b_kΦ₀^k, deg b_k < d₀, with w₀(b₀) = h₀,
c′ := res(b₀/π^{h₀}) ≠ 0, and w₀(b_k) ≥ amin(k) := ⌈(e₀−k)h₀/e₀⌉ (k ≥ 1;
strict-above automatic, gcd(e₀,h₀) = 1). Stratification by the residue c′:

* c′ = c₀ — the LAWFUL class of ψ₀ (wave-18's slice: measured exact, 0/104,404);
* c′ ≠ c₀ — the lawful class of the ξ-CONJUGATE ψ₀^{(ξ)} := ξ^{−1}ψ₀(ξy)
  = y + c₀/ξ at ξ := c₀/c′; letters z₁ = ξ·z₁′, z₁′ := −c′. This is exactly
  W-2 clause 3's ψ-transport, DEGENERATE at the corner: K₁ = K₀ carries no
  letter, so the tower transport is the bare scalar substitution z₁ ↦ z₁′
  (the clause-3 re-coordination step is vacuous). The ε-degeneration the
  charge names: ε₁-corrections are z₁-powers of a scalar, so the whole
  value layer transports by one character — the χ-law.

**CANDIDATE (the transport law, preregistered).** On the tower built on ANY
orbit member Φ′ (ledger transported: ψ₀ ↦ y + c′, all deeper data
byte-identical, canonical Φ₂ rebuilt on the transported letter), the accepted
2-read display holds WITH THE LETTER THE LIFT CARRIES:

    c′(γ,γ′) = z̄^{δ₂} · (z₁′)^{D₁},   D₁ := (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀,
    equivalently  c_base(γ,γ′) = c′(γ,γ′) · ξ^{D₁}   (the χ-ratio law),

with all integer data (splits, D₁, δ₂, windows) lift-independent. The ξ = 1
slice is wave-18's measured law; the ξ ≠ 1 direction is NEW — no instance
evidence exists anywhere in the corpus before this battery.

## S2. Sealed prediction sheet (`liftcorner_checks.py`, seed 20260911)

Roster: the wave-18 rows CA–CF verbatim (all g₀ = 1, E₂ ∈ {4,6,8,6,10,3}),
× rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}; windows W1×W1 + mixed W1×W3. Twists
exist iff |K₀| > 2 (deterministic applicability: d₀ = 2 rows on all rings;
d₀ = 1 rows on p = 3 rings only; 16 twistable (ring,row) instances). Per
instance: c′-draws (≤ 2, deterministic enumeration) × variants {pure twist,
twist + dense tails/mids} = 48 twisted towers; plus the ξ = 1 dense controls
(rows CB/CF × 4 rings) and the 24 base (standard) towers for the χ-cache.

| family | content | prediction |
|---|---|---|
| Q1 GATE | every generated tower passes the lawfulness gate FOR ITS OWN ψ₀′ (residual = y + c′) | 0 failures |
| Q2 AV | ANCHOR-VAL with the transported ε₁′ (z₁′-powers), letters W1+W3 | 0 |
| Q3 TLAW | **THE CANDIDATE: measured cocycle = transported display (z₁′)** | 0 |
| Q4 PV | L7 PAIR-VAL both forms + single-slot shape, transported letters | 0 |
| Q5 INT | exponent integrality | 0 |
| Q6 LOC | δ₁ = 0 sub-violations (lift-form-free legs; bug detector) | 0 |
| Q7 CHI | cross-tower χ-ratio: c_base == c′·ξ^{D₁}, measured vs MEASURED | 0 |
| Q8 COV | per twisted block: ≥ 1 δ₁ = 1 pair AND ≥ 1 pair with ξ^{D₁} ≠ 1 | met |
| Q9 WRONGLET | control: per-pair (c′ ≠ wrong-letter form) ⟺ (ξ^{D₁} ≠ 1), exact set equivalence; total fires > 0 | 0 / fires |
| Q10 XI1 | the ξ = 1 dense slice reproduces the UNCHANGED display (wave-18 tie) | 0 |
| TRS | closed-form transcription vs C.iter_law (transported automatically) | 0 |
| CERT | base towers: G.T1_T2(nf=4) + G.T5 internal (PARI leg NOT re-run: wave-18 T11 on the same base roster is on file — disclosed reuse) | 0 |
| ENG-GATE | engine_ext.agreement_gate(full=False) re-run in-unit (standing rule) | 0 new |

**Disclosures (pre-seal):** (a) a `--shakedown` crash-freedom run (1 ring,
2 rows, 1 twist, no json) runs before commit 1; (b) exact arithmetic,
deterministic full windows, no sampling beyond the seeded pert residues;
(c) the ledger override (ψ₀ ↦ y + c′) is IN-MEMORY on a fresh Tower object —
sound because at g₀ = 1 the degree-1 extension arithmetic of K₁ is
modulus-independent (mk_field_ext at g = 1: products never touch the reducer),
so ψ₁ and every deeper byte carries over verbatim; the runner asserts this
(ψ₁ bytes equal, K₂ arithmetic representation shared) before any comparison;
(d) SP bug-detector counters recorded.

## S3. VERDICT (commit 2; from the artifacts; seal dafc0b5, runner
byte-untouched, md5 ccb4351c92573f5f962cae4ae952d8dd)

**ALL GREEN, FIRST RUN, exit 0** — 25,409 checks, **0 violations in every
family**, elapsed 4.4 s (`liftcorner_checks_output.txt`,
`liftcorner_checks_results.json`; these govern on any transcription
discrepancy):

* Q1 GATE 56/56 orbit towers pass the lawfulness gate for their OWN ψ₀′
  (48 twisted + 8 ξ = 1 dense controls — exactly the deterministic
  applicability counts of the sheet); Q2 AV 656/0;
* **Q3 TLAW 4,176/0 — THE CANDIDATE: the display holds with the letter the
  lift carries (z₁′ = −c′) on every ξ-twisted tower**, both pair blocks;
* **Q7 CHI 4,176/0 — the χ-ratio law c_base = c′·ξ^{D₁} EXACT, measured
  against measured** (no closed form in the comparison): the W-2 covariance
  carries the corner;
* Q4 PV / Q5 INT / TRS 4,176/0 each; Q6 LOC 0 (no δ₁ = 0 anomaly);
* Q8 COV met — min 6 δ₁ = 1 pairs and min 6 teeth pairs (ξ^{D₁} ≠ 1) per
  twisted block; Q9 WRONGLET: per-pair set equivalence EXACT on 3,816
  samples, total fires 1,576 > 0 (the wrong-letter form fails exactly where
  ξ^{D₁} ≠ 1 — the transport is sharp, not slack);
* Q10 XI1: the ξ = 1 dense slice reproduces the unchanged display (wave-18
  tie re-confirmed); CERT internal 0; ENG-GATE 0 new (full=False disclosed);
  SP bug-detector 0.

STATUS EFFECT of S3 alone (before S4): the ξ ≠ 1 orbit direction — where NO
corpus evidence existed — is now MEASURED-TRANSPORT-EXACT: the displays
change under the lift orbit by EXACTLY the χ-law, W-2 clause 3's prediction
degenerate at the corner. The S4 compose is earned per the seal condition.

## S4. THE COMPOSE (earned by S3; the shift-descent route)

Setting: the S1 corner (g₀ = 1, e₀ ≥ 2; at e₀ = 1 no Case II exists —
COR-3's degeneration, theorem-backed, outside this unit). Φ′ an orbit member
with residue c′; Φ″ := Φ₀^{e₀} + lift(c′)·π^{h₀} the STANDARD lift of
ψ₀^{(ξ)} = y + c′. Base facts as [IL S1]/[ILN] S0.2 (division algorithm by
monic keys, w₀ a valuation, res additive + kills strict π-excess), plus:

**CONTENT (sub-lemma).** For monic Φ, the digits of dev(F, Φ) satisfy
w₀-content ≥ w₀-content(F). *Proof:* induction through the division step —
each subtraction removes lc(F)·x^i·Φ with lc(F) a coefficient of the current
remainder; w₀ is a valuation. ∎

### S4.1 LEMMA (TAIL-STAB) — the wave-18 open step, closed

For X = a·Φ₀^m·Φ′^j (a ∈ O[x], deg a < d₀) put the LEDGER weight
ω(X) := e₁(e₀·w₀(a) + m·h₀) + j·γ₂, γ₂ = e₁e₀h₀ + h₁. Then in the double
development X = Σ_j A_jΦ′^j, A_j = Σ_i a_{ji}Φ₀^i (dev by Φ′ then Φ₀):

    (LEDGER)  every nonzero digit obeys e₁(e₀·w₀(a_{ji}) + i·h₀) + jγ₂ ≥ ω(X).

Hence w₂(X) ≥ ω(X), and for any read weight Γ < ω(X) every level-2 read of X
at Γ contributes 0 at every grid slot (on-line: strict-excess summands die in
res; off-line: C_j = 0; digit collisions: w₀ ultrametric, min bounds survive).

*Proof.* Strong induction on m. **Base m < e₀:** deg(aΦ₀^m) < (m+1)d₀ ≤
e₀d₀ = deg Φ′, so by dev uniqueness the double dev is the single digit a at
(i, j) = (m, j): equality. **Step m ≥ e₀:** one pass of the orbit identity
Φ₀^{e₀} = Φ′ − b₀ − Σ_{k≥1}b_kΦ₀^k gives X = aΦ₀^{m−e₀}Φ′^{j+1} −
ab₀Φ₀^{m−e₀}Φ′^j − Σ_{k≥1} ab_kΦ₀^{m−e₀+k}Φ′^j; re-digit each level-0
coefficient (deg(ab) < 2d₀: dev = r + qΦ₀, CONTENT bounds both). Every child
is again of the lemma's shape with m′ ≤ m−1 (strict descent; termination),
and the ledger GAINS per branch (using e₀·amin(k) ≥ (e₀−k)h₀ + 1, forced by
gcd(e₀, h₀) = 1: e₀ | kh₀ ⟺ e₀ | k, impossible for 1 ≤ k < e₀):

| branch | (m′, j′) | ω-gain ≥ |
|---|---|---|
| key | (m−e₀, j+1) | γ₂ − e₁e₀h₀ = h₁ > 0 |
| b₀-main ĉ′π^{h₀}, r/q digit | (m−e₀ / m−e₀+1, j) | 0 / e₁h₀ |
| b₀-tail t₀ (w₀ ≥ h₀+1) | (m−e₀ (+1), j) | e₁e₀ |
| mid b_k (w₀ ≥ amin(k)) | (m−e₀+k (+1), j) | e₁ |

IH on each child + dev-linearity (the double dev of X is the digit-wise sum
of the children's) + the ultrametric close (LEDGER). The ONLY 0-gain branch
is b₀-main's r-digit, which also strictly drops m: the ω(X)-thread
terminates in ≤ ⌈m/e₀⌉ passes. ∎ [This IS the shift-descent bookkeeping:
one key up costs h₁, exactly the χ-chain's descent step (GRTW2 §3.4 rem. 1);
the window-calculus ledger ω is the tail-weight bookkeeping ILNRES S5.1
priced. Machine mirror: Q3/Q4 — the tail never reaches the read.]

### S4.2 LEMMA (READ-EQ) — the Φ′-tower reads = the Φ″-tower reads

Every 2-read battery object (anchors φ_γ = π^{u₁}Φ₀^{s₁}K^{s₂}; pair
products φ_γφ_{γ′}; K = the tower's own key) has IDENTICAL level-2 reads
(weight, grid, every slot coefficient) on the Φ′- and Φ″-towers. *Proof.*
The towers share every read datum (reads, ψ₁, K₂, and the LETTER z₁′ = −c′
in ε₁) — only key bytes differ. (a) Anchors and δ₁ = 0 products are
π^uΦ₀^sK^S with s < e₀ < deg: single K-slot coefficient π^uΦ₀^s — identical
bytes, the key power never opened (any δ₂-carry is grid bookkeeping, no
reduction at the top level of a 2-read). (b) δ₁ = 1 products (g₀ = 1 ⟹
s₁+s₁′ ≤ 2e₀−2: EXACTLY one overflow): P = π^UΦ₀^{e₀+S₁″}K^{S₂},
ω(P) = Γ := γ+γ′ (the split identity γ = e₁(e₀u₁+s₁h₀) + s₂γ₂). One pass on
each tower; compare children. Key child π^UΦ₀^{S₁″}K^{S₂+1}: identical
bytes, ledger Γ+h₁ — strictly above on BOTH towers (reads 0 both; it is the
E₁ digit). b₀-main children: −π^{U+h₀}ĉ′Φ₀^{S₁″}K^{S₂} vs
−π^{U+h₀}lift(c′)Φ₀^{S₁″}K^{S₂}: single digits; their difference has
w₀(ĉ′−lift(c′)) ≥ 1 (both lift c′), ledger ≥ Γ + e₁e₀. Φ′-only children
(t₀, mids): ledger ≥ Γ+1, and by TAIL-STAB every digit they generate stays
> Γ. So the on-Γ-line digit content coincides; all deviations are strict
π-excess at their slots; res kills them and the ultrametric keeps w₂ = Γ and
the on-line status equal on both sides. Reads agree slot-by-slot. ∎

### S4.3 THEOREM (the corner discharge) and the two corollaries

**THEOREM.** For EVERY orbit member Φ′ (any residue c′ ≠ 0), the 2-read
ITER-LAW display holds on the Φ′-tower with the letter the lift carries:
c(γ,γ′) = z̄^{δ₂}·(z₁′)^{D₁}, z₁′ = −c′, all γ,γ′ ∈ W₂. *Proof.* READ-EQ
transports every anchor value, pair value and cocycle to the Φ″-tower; Φ″ is
a STANDARD-LIFT instance of the accepted class with ψ₀ ↦ ψ₀^{(ξ)} (same
(e,h,g) data, ψ₀^{(ξ)}(0) = c′ ≠ 0), where the ACCEPTED ITER-LAW gives the
display with its letter z₁′. ∎ [Machine: Q3 4,176/0.]

**COR 1 ((ITER-LAW-LIFT), the corner).** ξ = 1 slice (c′ = c₀): the display
holds UNCHANGED for every LAWFUL monic lift — the 2-read (ITER-LAW-LIFT) is
proved at g₀ = 1 ∧ δ₁ = 1, exactly where it was open (ITERLAW S7: only
PAIR-VAL Case II consumes Φ₁'s form; all other strata lift-form-free).
[Machine: Q10 + wave-18's 104,404/0.]

**COR 2 (the χ-covariance).** Across the orbit the display transports by
z₁ = ξ·z₁′ alone: c_base = c′·ξ^{D₁}. This is W-2 clause 3's value-layer
statement (W2-OPEN-1) RESTRICTED to the base junction at the corner — now
PROVED at this note's grade there, upgraded from instance-confirmed.
[Machine: Q7 4,176/0 measured-vs-measured; Q9 sharpness 1,576 fires exact.]

**PROP (propagation to every level — the S0.1 rider leg).** (ITER-LAW-n)
for every lawful monic Φ₁ at the corner, all n: the [ILN] chain consumes
Φ₁'s explicit bytes only through (i) monicity/degree/w₁Φ₁ = e₀g₀h₀ (shared
by every orbit member) and (ii) the level-1 base package (= [IL], replaced
here by COR 1; at n = 1 clause (ii) is ITERLAW S7's own display). Riding
S0.1's verbatim propagation, the discharge lifts to every rung AT [ILN]'s
OWN conditionality (T-class/(RM-m)/DCX ledger unchanged). VERIFY-TARGET for
the arc: the clause-(ii) census at rungs ≥ 2 (no rung leg opens Φ₁'s bytes
outside the level-1 package) is cited from the [ILN]/ILNRES consumption
tables, not re-proved here.

**Grade box + W-2 consumption census (the cap).** This note: ATTEMPT 0/2,
hostile arc OWED (charge: the CONTENT sub-lemma's base-fact status; the
READ-EQ on-line-content/ultrametric close; PROP's census cite). W-2
consumption: COR 2 and the S1 orbit frame consume GRTW2 clause 3 (the
ψ-transport definition + its corner degeneration) — GRTW2 is itself 0/2, so
**the unit's grade is CAPPED at that consumption, as charged**. Honest
decoupling fact the arc may use: the COR 1 chain (TAIL-STAB + READ-EQ +
accepted ITER-LAW) is W-2-free — if W-2's arc lags, the ξ = 1 discharge
stands on this note's own arc alone.

## S5. Consequence display (what [ILN]'s rider becomes; at the capped grade, pending arcs)

ONCE THIS NOTE'S ARC CLOSES (and not before — no ledger or accepted text is
edited now): ITERLAWN S0.1's rider "(ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; nothing is claimed for any non-canonical lawful lift at any
level" becomes, on the Φ₁ axis: "(ITER-LAW-LIFT) DISCHARGED at attempt grade
(capped by the W-2 0/2 consumption; ξ = 1 core W-2-free): ITER-LAW-n holds
for EVERY lawful monic Φ₁, every n, at [ILN]'s own conditionality, and
covariantly for the full Φ₁-orbit by the χ-law". NR-1 then leaves the
ILNRES residual list; the T-class(n) conditionality of record shrinks to
NR-2/NR-3 (+ NR-4's own closing arc). NOT covered, said plainly:
non-canonical lawful lifts at DEEPER levels (Φ_{m+1}, m ≥ 1) — a separate
corner (the g_m = 1 analogue), never part of (ITER-LAW-LIFT)'s displayed
statement (wave-18 S0), stays open as its own priced item. The wave-18
sketch's one open step (TAIL-STAB) is CLOSED by S4.1 (its ω is this ledger;
the monomial form is subsumed); wave-18's price sheet is settled in full.

— LIFT-CORNER unit, campaign date 2026-08-08 (wallclock 2026-08-04).
