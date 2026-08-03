# ITER-LAW-r LEVEL-3 COCYCLE PROBE — sealed preregistration: the composed three-constant candidate c₃(γ,γ′) = z̄^{δ₃}·z₂^{D₂}·z₁^{D₁} on standard-lift 3-read towers, with the composed inner shift Σ = D₂γ₂ + δ₃γ₃(ℓ₁′−ℓ₁w₁Φ₁) DISTINGUISHED from the naive per-level template

**Unit:** WAVE-18 UNIT 2 = synthesis-8 queue #2 (charter `docs/SYNTHESIS_PASS8_2026-08-08.md`
S3(i) + S4 item 2: "extend the harness to 3-level towers (standard lift), preregister the
composed-cocycle law ... SEALED pre-run, measure on e₂ ≥ 2 and e₀ ≥ 2 stacked strata +
mixed blocks (the COR-4 lesson: include mixed blocks in the FIRST battery)"). PROBE-FIRST:
the product of this unit is a MEASURED-LAW VERDICT, not a proof note; no compose unit
charters without a wave-19 charter. **Two-commit seal:** this file's S0–S4 + the runner
`verification/openmath/iterlawr_probe.py` are committed BEFORE any battery run (commit 1);
the S5 verdict block + outputs land at commit 2. Design-phase disclosure: the runner's
`--design` mode (tower construction + constants table ONLY, no law comparison, no val₃
computed on any pair) and `py_compile` are run pre-seal, per the strata3e2_design.py
precedent. Seed: **20260903** (fresh; never used in this genre). Author: Fable, wave-18
unit 2, campaign date 2026-08-08 (wallclock 2026-08-03).

## S0. Authority, class pin, and the harness of record

**The accepted order-2 base (citation PASTED from the ledger defined-term block,
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "ITER-LAW ACCEPTED — 2026-08-03"):**
"Scope as accepted: the harness tower class (superset of DITER_RESTATE §S2's E₂ > 1 pin;
on-the-nose coincidence restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3 untouched."
This probe operates in the third residual's territory (orders ≥ 3 = untouched) — nothing
here consumes or upgrades the accepted statement; on a GREEN verdict the level-3 law is a
MEASURED LAW (instance-confirmed conjecture), nothing more.

**The harness calculus of record (definitions consumed VERBATIM, no reimplementation):**

* Levels 0–2: `grb_order2_check.Tower` (standard lift Φ₁, grb_order2_check.py:499–507;
  canonical ε₁-corrected lift Φ₂ = `build_Phi2`, :648–658, T5-certified R₂(Φ₂) = ψ₁;
  eq12/bezout :448–463; R1w/eps1(reading C)/R2w :556–623). This is the exact calculus the
  ACCEPTED ITER-LAW note pins as its S0 setting (ITERLAW_2026-08-08.md:46–89).
* Level 3: `strata3_probe.Tower3` (strata3_probe.py:225–330; inherited verbatim by the
  TWIST-3 probe): ε₂(β) := z₂^{ℓ₁′s−ℓ₁u}, (s,u) = eq12(β,e₁,h₁), reading C one level up
  (:248–252); w₃(f) := min_j{e₂·w₂(a_j) + j·γ₃} over the Φ₂-development (:266–275);
  R₃-read R3w (:278–302) with slot grid s₃ + je₂, slot weights γ_j = (γ−s_jγ₃)/e₂,
  coefficient C_j = ε₂(γ_j)·R2v(a_{s_j}) on-line (R2v = the level-2 read evaluated at
  y ↦ z₂, :255–264); γ₃ := e₂·w₂Φ₂ + h₂, w₂Φ₂ = e₁g₁γ₂; Φ₃ = `build_Phi3` (CERT-only
  here — the cocycle does NOT consume Φ₃).
* NEW in this unit (the only added calculus, mirroring the level-2 val):
  K₃ := K₂[z̄]/(ψ₂) via `mk_field_ext`; **val₃(f) := Σ_j R3w(f)_j · z̄^j ∈ K₃** (the
  level-3 read evaluated at y ↦ z̄); the level-3 canonical anchors and cocycle (S1).

**Class pin (the probed class).** Standard-lift 3-read towers in the harness sense at
every level: Φ₀ monic with irreducible reduction, Φ₁ the standard lift of ψ₀, Φ₂ the
canonical ε₁-corrected lift (R₂(Φ₂) = ψ₁ exact), reads (e₀,h₀,ψ₀), (e₁,h₁,ψ₁),
(e₂,h₂,ψ₂) with gcd(eᵢ,hᵢ) = 1, ψᵢ monic irreducible with ψᵢ(0) ≠ 0; E₃ := e₀e₁e₂;
normalized Bézout pairs (ℓ₀,ℓ₀′), (ℓ₁,ℓ₁′). The (ITER-LAW-LIFT) residual propagates: this
probe says NOTHING about non-standard lawful lifts at any level. All roster rows have
E₃ ≥ 4.

**The level-3 anchor alphabet (the iterated eq-(12-int) split, one level up from
DITER_RESTATE §S2's).** For γ ∈ ℤ:

    (s₃,u₃) := eq12(γ, e₂, h₂);       β₂(γ) := u₃ − s₃·w₂Φ₂    [so γ = e₂β₂ + s₃γ₃]
    (s₂,u₂) := eq12(β₂, e₁, h₁);      β₁(γ) := u₂ − s₂·w₁Φ₁    [so β₂ = e₁β₁ + s₂γ₂]
    (s₁,u₁) := eq12(β₁, e₀, h₀).

Anchor φ_γ := π^{u₁}·Φ₀^{s₁}·Φ₁^{s₂}·Φ₂^{s₃}; window W₃ := {γ : u₁(γ) ≥ 0}; the probe
windows are W1 = [Γ₀, Γ₀+E₃), W2 = W1+E₃, W3 = W1+7E₃ with Γ₀ ≡ 0 (mod E₃) fixed by a
deterministic design-time scan (u₁ ≥ 0 verified for every γ up to 3·(Γ₀+8E₃)+2, covering
all pair and triple sums). Sanity identity (checked in the symbolic leg): w₃(φ_γ) = γ;
φ_{γ+E₃} = π·φ_γ exactly. Cocycle:

    c₃(γ,γ′) := val₃(φ_γ·φ_{γ′}) / val₃(φ_{γ+γ′}).

## S1. THE CANDIDATE LAW (sealed; every constant named)

**(ITER-LAW-3) [THE PRIMARY CANDIDATE].** For all γ, γ′ ∈ W₃:

    c₃(γ,γ′) = z̄^{δ₃} · z₂^{D₂} · z₁^{D₁}

with the constants (all splits ITERATED as in S0):

    δ₃ := ⌊(s₃(γ)+s₃(γ′))/e₂⌋ ∈ {0,1}                                [top carry]
    D₂ := (s₂(γ)+s₂(γ′)−s₂(γ+γ′) + ℓ₁·γ₃·δ₃)/e₁ ∈ ℤ                  [middle exponent]
    Σ  := D₂·γ₂ + δ₃·γ₃·(ℓ₁′ − ℓ₁·w₁Φ₁) ∈ ℤ                          [composed inner shift]
    D₁ := (s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀·Σ)/e₀ ∈ ℤ                      [inner exponent]

where z̄ = the level-3 letter (K₃ = K₂[z̄]/(ψ₂)), z₂ = the level-2 letter
(K₂ = K₁[z₂]/(ψ₁)), z₁ = the frame letter (K₁ = K₀[z₁]/(ψ₀)), γ₂ = e₁·w₁Φ₁ + h₁,
γ₃ = e₂·w₂Φ₂ + h₂, w₁Φ₁ = e₀g₀h₀, w₂Φ₂ = e₁g₁γ₂, and (ℓ₀,ℓ₀′), (ℓ₁,ℓ₁′) the normalized
Bézout pairs at (e₀,h₀), (e₁,h₁).

**Provenance (the derivation this candidate was composed from — "L7 stacked on L7";
displayed here so a failure localizes).** The Φ₂-development digit of the anchor product
P = π^UΦ₀^{S₁}Φ₁^{S₂}Φ₂^{S₃} is A := π^UΦ₀^{S₁}Φ₁^{S₂} — which is EXACTLY a level-2
anchor pair product φ^{(2)}_{β₂}·φ^{(2)}_{β₂′} of the accepted note's L7. Stacking:

* L6-3 (anchor value): val₃(φ_γ) = ε₂(β₂(γ))·ε₁(β₁(γ)) ∈ K₃^× — the ε-chain.
* L7-3 (pair value): val₃(φ_γφ_{γ′}) = z̄^{δ₃}·ε₂(β₂+β₂′)·z₂^{δ₂}·z₁^{δ₁}·ε₁(β₁+β₁′)
  with δ₂ := ⌊(s₂(γ)+s₂(γ′))/e₁⌋, δ₁ := ⌊(s₁(γ)+s₁(γ′))/e₀⌋ — the inner two factors are
  the accepted L7 verbatim on the digit A; the top slot shift z̄^{δ₃} is the accepted
  Case-I slot-grid absorption one level up. Equivalent product form (W-MULT-3 shape):
  val₃(φ_γφ_{γ′}) = z̄^{δ₃}·val₃(φ_γ)·val₃(φ_{γ′}) (by EPS-MULT at both ε levels).
* INNER-SHIFT-3 (integer layer): β₂(γ+γ′) = β₂(γ)+β₂(γ′)+δ₃γ₃ (L1 at (e₂,h₂), verbatim
  L2 one level up), and the COMPOSED inner shift
  **β₁(γ+γ′) = β₁(γ)+β₁(γ′) + Σ**, Σ = D₂γ₂ + δ₃γ₃(ℓ₁′−ℓ₁w₁Φ₁), derived from
  e₁β₁ = β₂ − s₂(β₂)γ₂ plus 1−ℓ₁γ₂ = e₁(ℓ₁′−ℓ₁w₁Φ₁).
* EXP generalized (two lines, arbitrary shift): for β″ = β+β′+Σ,
  z₁^{δ₁}·ε₁(β+β′)/ε₁(β″) = z₁^{(s(β)+s(β′)−s(β″)+ℓ₀Σ)/e₀}; same at level 2 with
  β₂″ = β₂+β₂′+δ₃γ₃ giving z₂^{δ₂}·ε₂(β₂+β₂′)/ε₂(β₂″) = z₂^{D₂}. Dividing L7-3 by L6-3
  at γ+γ′ yields the display.

**THE DISTINGUISHED ALTERNATIVE (the naive per-level template — the literal S3(i)
reading).** Same z̄^{δ₃}, same D₂, but inner exponent

    D₁ⁿᵃⁱᵛᵉ := (s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀·γ₂·δ₂)/e₀,  δ₂ = ⌊(s₂(γ)+s₂(γ′))/e₁⌋.

The two coincide at δ₃ = 0 (there D₂ = δ₂ and Σ = γ₂δ₂) and differ in general at δ₃ = 1
(integer level: Σ − γ₂δ₂ = (D₂−δ₂)γ₂ + δ₃γ₃(ℓ₁′−ℓ₁w₁Φ₁) ≠ 0 generically). The probe
measures BOTH: the primary is the sealed prediction; the naive form's violation count and
the separation meters (integer-level and field-level) are recorded. If the primary fails
where the naive holds, the naive becomes the finding; if both hold on all instances
(possible only if every separation vanishes mod the letter orders), the verdict says so
honestly.

**What would falsify (ITER-LAW-3) — the explicit list.**
1. Wrong z̄-power: any pair with top-slot shift ≠ δ₃ = ⌊(s₃+s₃′)/e₂⌋ (e.g. keyed to e₁,
   or > 1, or weight-dependent).
2. Wrong middle fibration term: D₂'s ℓ₁γ₃δ₃ wrong (absent, wrong sign, ℓ₁′ instead of
   ℓ₁, γ₂ instead of γ₃) — G3/G4 violations concentrated at δ₃ = 1.
3. Wrong INNER fibration: Σ ≠ the composed shift — in particular the naive γ₂δ₂ — G3
   violations at δ₃ = 1 on z₁-teeth rows; the symbolic leg (G8) separates the integer
   forms unconditionally.
4. Wrong denominator: e₁ vs e₀ in D₂/D₁ (non-integrality events at G4, or wrong values).
5. Missing twist unit: ε₂ absent from the anchor value (G1 fails identically on ℓ₁ ≠ 0
   rows with z₂ ≠ 1).
6. Non-integrality: any pair where e₁ ∤ (s₂-defect + ℓ₁γ₃δ₃) or e₀ ∤ (s₁-defect + ℓ₀Σ).
7. Shape failure: level-3 read of an anchor product with ≠ 1 nonzero top slot, top slot
   ≠ δ₃, or weight ≠ γ+γ′.
8. Cascade strata: failures localized to the middle Case-II stratum (g₁ = 1 ∧ δ₂ = 1,
   where the Φ₂-development needs the canonical-lift reduction) or the double-cascade
   stratum (g₀ = g₁ = 1, inner spread to Φ₁-slot S₂+1 = e₁ overflowing deg Φ₂ even at
   δ₂ = 0) — the designed falsification surface; coverage metered, see S3.

A FAILURE IS A FULL SUCCESS OF THE PROBE: any surviving RED is reported with the exact
violating tuple (tower; γ, γ′; measured value; predicted value; constants) as the
headline. No post-hoc candidate edits inside this seal; a revised candidate = one new
sealed prereg cycle at most, clearly bracketed.

## S2. Tower roster (all fresh; none is a strata3/strata3e2/iterlaw roster row)

(tag, d₀; e₀,h₀,g₀; e₁,h₁,g₁; e₂,h₂,g₂) over all four rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}
(52 towers). Charter coverage: e₂ ≥ 2 rows (all but CX), e₀ ≥ 2 stacked rows
(A,B,C,E,F,G,H,K,L), mixed-e rows (B,D,F,L), an E₃ ≥ 16 row (L).

| row | data | E₃ | design point |
|---|---|---|---|
| A | (1; 2,1,1; 2,1,1; 2,1,1) | 8 | fully stacked, g₀=g₁=1: DOUBLE-CASCADE live |
| B | (1; 3,2,1; 2,1,1; 2,1,1) | 12 | e₀=3, ℓ₀=2 nontrivial; inner Case II; double cascade |
| C | (1; 2,1,2; 2,1,1; 2,1,1) | 8 | g₀=2: K₁ genuine ext (z₁ ord > 1 at p=2), inner Case I |
| D | (1; 2,1,1; 3,1,1; 2,1,1) | 12 | e₁=3 middle, ℓ₁=1; middle Case II at e₁=3 |
| E | (1; 2,1,1; 2,1,2; 2,1,1) | 8 | g₁=2: K₂ genuine ext (z₂ teeth); middle Case I |
| F | (1; 2,1,1; 2,1,1; 3,2,1) | 12 | e₂=3, h₂=2: nontrivial top track (s₃ ∈ {0,1,2}) |
| G | (1; 2,1,1; 2,1,1; 2,1,2) | 8 | g₂=2: K₃ genuine ext (z̄ teeth); level-3 value-set record |
| H | (2; 2,1,1; 2,1,1; 2,1,1) | 8 | d₀=2 base inertia |
| K | (1; 2,3,1; 2,3,1; 2,3,1) | 8 | all hⱼ=3: nontrivial h-track at every level |
| L | (1; 2,1,1; 2,1,1; 4,3,1) | 16 | e₂=4, h₂=3: THE E₃ ≥ 16 row, deep top carry track |
| CV | (1; 1,1,2; 2,1,1; 2,1,1) | 4 | e₀=1 CONTROL: predicted c₃ = z̄^{δ₃}·z₂^{D₂} (s₁ ≡ 0, ℓ₀=0) |
| CW | (1; 2,1,1; 1,1,2; 2,1,1) | 4 | e₁=1 CONTROL: D₂=0, Σ=δ₃γ₃; c₃ = z̄^{δ₃}·z₁^{(s₁-def+ℓ₀γ₃δ₃)/e₀} |
| CX | (1; 2,1,1; 2,1,1; 1,1,2) | 4 | e₂=1 CONTROL: δ₃=0; c₃ = the ACCEPTED level-2 law in letters (z₂,z₁), tied to SP.Composite by embedding (F0b) |

ψ₀, ψ₁ picked by the Tower's deterministic pick_irreducible (idx conventions verbatim);
ψ₂ by Tower3's pick_irr3 (idx = (h₀+h₁) mod 2) THROUGH a disclosed deterministic shim in
the runner (pick_irr3 early-exits without index wraparound, so idx=1 over a field with a
single eligible degree-1 irreducible — e.g. ψ₂ over K₂ = F₂ on row B — raises; the shim
retries idx=0 on exhaustion; strata3_probe.py is byte-untouched; found at the design-phase
construction dry-run, pre-seal). All g₂ ≤ 2 (pick_irr3 irreducibility test bound).
Design-mode dry run (pre-seal, disclosed): all 52 towers construct; window bases Γ₀ per
the runner's `--design` table (e.g. A: 48, B: 144, L: 192, CX: 16; scan guarantees
u₁ ≥ 0 through 3·(Γ₀+8E₃)+2).

## S3. Preregistered falsifier legs and predictions (violation counts; RED = obs ≠ pred)

F0a LEVEL-2 FIDELITY: the ACCEPTED ITER-LAW closed form (z̄→z₂ letter) on the level-2
    subtower SP.Composite(T3.T), its own W×W block, measured cocycle vs closed form —
    all 13 rows × 4 rings. If this leg is RED the HARNESS is wrong, not the law.
                                                              PREDICTED: 0.
F0b CX EMBED TIE (e₂ = 1): c₃(γ,γ′) == K₃-embed of the level-2 measured cocycle
    c₂(γ,γ′) at the same (γ,γ′), full W1×W1 table.            PREDICTED: 0.
G1  L6-3 ANCHOR-VAL: val₃(φ_γ) == embed(ε₂(β₂)·ε₁(β₁)) ≠ 0, every letter of W1, W2, W3.
                                                              PREDICTED: 0.
G2  L7-3 PAIR-VAL, blocks W1×W1, W3×W3, W1×W3, BOTH forms:
    (a) val₃(φφ′) == z̄^{δ₃}·embed(ε₂(β₂+β₂′))·z₂^{δ₂}·z₁^{δ₁}·embed(ε₁(β₁+β₁′)),
    (b) val₃(φφ′) == z̄^{δ₃}·val₃(φ)·val₃(φ′)  [W-MULT-3 shape],
    plus the shape clause: single nonzero top slot, at slot δ₃, weight γ+γ′.
                                                              PREDICTED: 0.
G3  THE CANDIDATE (ITER-LAW-3): measured c₃ == the S1 primary closed form, same blocks.
    Naive-form comparison recorded per pair (violation count reported, NOT part of the
    primary prediction; separation meters MSEPf/MSEPi below).  PREDICTED: 0 (primary).
G4  Integrality: e₁ | (s₂-defect + ℓ₁γ₃δ₃) and e₀ | (s₁-defect + ℓ₀Σ), all block pairs.
                                                              PREDICTED: 0.
G5  Cocycle identity (associativity): c₃(a,b)c₃(a+b,t) == c₃(b,t)c₃(a,b+t), 216 sampled
    triples from W1 per tower, measured AND closed form.       PREDICTED: 0.
G6  Degenerations on CV (e₀=1), CW (e₁=1), CX (e₂=1) per the S2 table displays, all
    block pairs of those rows.                                 PREDICTED: 0.
G7  ℤ/E₃ descent incl. MIXED blocks (the COR-4 lesson, FIRST battery): the (r,s) table
    on W2×W2 and W3×W3 equals W1×W1, AND all four mixed blocks W2×W1, W1×W2, W3×W1,
    W1×W3 equal it entrywise.                                  PREDICTED: 0.
G8  Integer layer, 20,000 symbolic draws (pure ℤ, no field; eⱼ ≤ 12, hⱼ ≤ 39, gⱼ ≤ 4):
    L1 at all three levels; INNER-SHIFT-3 (β₂″ = β₂+β₂′+δ₃γ₃); the composed-shift
    identity β₁″ = β₁+β₁′+Σ with D₂ ∈ ℤ; D₁ ∈ ℤ; generalized EXP at both levels
    (exponent assembly == closed constants).                   PREDICTED: 0.
CERT2 level-2 subtower certification, all rows: G.T1_T2 (nf=6), G.T5, G.T11 (PARI
    factorpadic, ℤ_p instances).                               PREDICTED: 0.
CERT3 level-3 data: ψ₂ monic/irreducible/ψ₂(0)≠0/gcd(e₂,h₂)=1; Φ₃ monic, deg = e₂g₂·deg Φ₂,
    w₃(Φ₃) = e₂g₂γ₃, no slot below weight, R₃s(Φ₃) == ψ₂ exact (the V4 key check one
    level up); PARI leg on ℤ_p instances: Φ₃ irreducible over ℚ_p, one prime,
    (e,f) = (E₃, d₀g₀g₁g₂).                                    PREDICTED: 0.

METERS (teeth/coverage; MATCH conditions, sealed):
  MC-inner  pairs with g₀=1 ∧ δ₁=1 (inner Case II)   > 0 on rows A, B (each ring).
  MC-mid    pairs with g₁=1 ∧ δ₂=1 (middle cascade)  > 0 on rows A, B, D, F, L (each ring).
  MC-dbl    pairs with both                          > 0 on rows A, B (each ring).
  MV        pairs with predicted c₃ ≠ 1 (visibility) > 0 on rows C, E, G (each ring).
  MSEPi     G8 draws with Σ ≠ γ₂δ₂ (integer separation of primary vs naive) > 0.
  MSEPf     block pairs where primary ≠ naive AS FIELD VALUES: reported (expected > 0
            somewhere; 0 ⟹ the instance battery cannot separate them — honesty display,
            not a RED).
  MD3       pairs with δ₃ = 1 > 0 on every e₂ ≥ 2 row (the top carry exercised).

MUTATION CONTROLS (post-battery, same runner, same seal; reduced battery = rows B, D, E,
F over rings (ℤ₃, F₂[[t]]), W1×W1 blocks + G1; each mutation applied to the CLOSED FORM
(m5: to the G1 prediction) and required to be DETECTED (≥ 1 violation), else the battery
lacks teeth for that constant → verdict PARTIAL):
  m1 drop ℓ₁γ₃δ₃ from D₂ (Σ recomputed from mutated D₂)        PREDICTED: detected.
  m2 Σ → γ₂·δ₂ (THE NAIVE TEMPLATE as a mutation)              PREDICTED: detected.
  m3 D₂ denominator e₁ → e₀ (teeth: rows B, D where e₀ ≠ e₁)   PREDICTED: detected.
  m4 δ₃ → ⌊(s₃+s₃′)/e₁⌋ (wrong modulus; teeth: D, F, e₁ ≠ e₂)  PREDICTED: detected.
  m5 drop ε₂ from the G1 anchor prediction (teeth: row E)      PREDICTED: detected.
  m6 letter swap z₂ ↔ z₁ (z̄^{δ₃}z₁^{D₂}z₂^{D₁}; teeth: row E)  PREDICTED: detected.

DISCIPLINE: exceptions (harness asserts) are HARNESS EVENTS, recorded per tower and
counted separately — a harness event is a bug-detector firing, classified before any law
verdict; CERT/F0 rows are bug detectors first. Exit 0 iff all predicted-0 families are 0,
all MATCH meters met, all mutations detected, no harness events. DETERMINISTIC:
random.seed(20260903), exact arithmetic only. JSON: iterlawr_probe_results.json.

## S4. What this probe does NOT claim (fences)

* No proof: a GREEN verdict makes (ITER-LAW-3) a MEASURED LAW (instance-level), the
  compose unit is a separate wave-19 charter. Numerics are falsifiers, never proofs.
* No orders ≥ 4 claim; no general-lift claim ((ITER-LAW-LIFT) propagates to every level);
  no gr(w₃) semantics claim (the wrapper story stays consumer-side); no GMN-side claim
  (this battery is FGMN-calculus-internal; GMN transport = the TWIST-3/TR3-S4 lane).
* No edits to any accepted record; DITER_RESTATE/ITERLAW/TWIST3 files untouched.
* The θ_j = ℓ_{j−1}g_{j−1}γ_j twist units of the S3(i) sketch are the KEY-transport unit
  part (TWIST-3 lane), not the cocycle constants; they are not probed here.

## S5. VERDICT (post-run; commit 2 fills this block — PENDING at the seal)

**PENDING.** Nothing below this line is written before the sealed battery has run.

