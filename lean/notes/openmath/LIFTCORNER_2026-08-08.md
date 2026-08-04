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

## S4. THE COMPOSE (written only on a green S3, per the seal condition)

[PENDING — the (TAIL-STAB) proof, Case II′, the corner discharge theorem, the
W-2 clause-2/3 consumption display, and the honest propagation leg.]

## S5. Consequence display (what [ILN]'s rider becomes)

[PENDING — displayed with S4, at the capped grade.]

— LIFT-CORNER unit, campaign date 2026-08-08 (wallclock 2026-08-04).
