# STRATA PROBE — the two untested strata adjudicated: the corrected-ǫ twist law at e₀ ≥ 2 CONFIRMED (closed form measured exact), the D-ITER composite's single-constant CYCLIC presentation REFUTED at the canonical alphabet (true law displayed)

**Unit:** Tier-3 STRATA FALSIFIER, hardest-first order item 5
(`docs/HARDEST_FIRST_ORDER_2026-08-08.md`), falsifier-first per the standing
concrete-trace discipline: both strata probed BEFORE any proof unit is written.
**Harness:** `verification/openmath/strata_probe.py` (preregistration in the
script header, fixed before the run; output `strata_probe_output.txt`, JSON
`strata_probe_results.json`; deterministic seed 20260815, exact arithmetic,
PARI oracle on the new tower rows).  **Parents:** GRB leaf
`GRB_ORDER2_2026-08-05.md` (S3.4(ii) two-stratum conjecture; S5.3 D-ITER),
`TR3S1_2026-08-08.md` (the e₀ = 1 theorem this extends off-stratum),
`MOVES_2026-07-24.md` §§F.0/F.2 (the composite display), N-1
(`grb_order2_check.py`, machinery reused; corrected Def 3.15 = the
triple-pinned reading — the raw fgmn.txt rendering at Def 3.15 is corrupted
and was not consulted).  **Author:** Fable strata-falsifier unit, campaign
date 2026-08-08 (wallclock 2026-08-02).

## S0. Verdict table (all preregistered rows; samples in parentheses)

| row | claim | status going in | observed | verdict |
|---|---|---|---|---|
| A0 | GMN-side integrity (t₁ ∈ ℤ, component shape, cᵢ ≠ 0 on-line) | sealed (GMN's printed proofs) | 0/20,828 | GREEN |
| A1 | support agreement FGMN vs GMN | conj component | 0/7,255 | GREEN |
| A2 | Lemma-A-general (inner read = z₁^{m₀}·GMN inner read) | conj component | 0/4,297 | GREEN |
| A3 | **(TWIST-LAW)** C^F_j = z₁^{ℓ₀g₀h₀·s_j}·c^G_{s_j} | **THE PROBED CONJECTURE** | 0/3,640 | **GREEN** |
| A5 | e₀ = 1 controls: identity | sealed (TR3-S1) | 0/1,252 | GREEN |
| A6 | naive identity C^F = c^G REFUTED at every twist-visible slot | derived from A3 | 1,023/1,023 | MATCH |
| A7 | retired S3.2-shape increment z₁^{γ₂} refuted on discriminating pairs | derived | 293/293 | MATCH |
| B0a | cocycle identity (associativity) — bug detector | must-hold | 0/2,732 | GREEN |
| B0c | representative independence | sealed | 0/804 | GREEN |
| B1 | alphabet/shape laws (letters = ǫ₁-values, pair reads at y^{δ₂}) | sealed | 0/1,984 | GREEN |
| B2 | **(ITER-LAW)** composite structure constants | derived this unit | 0/804 | **GREEN** |
| B3 | e₀ = 1 CYC controls (D-REAL: ζ′ = z̄) | sealed | 0/52 | GREEN |
| CERT | designed rows K/L/M/N certified (T1/T2/T5 + T11 PARI) | sealed | 0/344 | GREEN |
| B3-adj | **(CYC) single-ζ′ cyclic presentation at mixed strata** | **THE PROBED DISPLAY** | NOT-CYCLIC 22/28 | **ADJUDICATED FALSE** |

Perimeter: 13 tower rows (N-1's A–J minus F, plus designed K (2;2,1,1;2,1,1),
L (2;3,2,1;2,1,1), M (2;2,1,2;3,1,1), N (2;2,1,1;2,1,2) — multiplicatively
rich residue data so the twist is VISIBLE; the G2 lesson) over all four base
rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}; E₂ up to 6, deg Φ₂ up to 24.  Exit code 0
(every preregistered row at its predicted count).  One build-phase
adjudicator bug (rep/label misalignment in the CYC relabeling equation) was
caught BY the preregistered sealed-control row B3 on the first full run and
fixed; the amendment is displayed in the script header; values/laws B0–B2
were unaffected.

## S1. Family A — the corrected-ǫ twist law at e₀ ≥ 2 (TR3-S1's analogue off the unramified stratum)

**Setting.** Order-2 tower (GRB S1.1), reads (e₀,h₀,ψ₀), (e₁,h₁,ψ₁); FGMN
weight-read coefficients C^F_j (Defs 3.16/3.18 with the CORRECTED Def 3.15,
harness reading C) at abscissas s_j = s₂ + je₁; GMN residual coefficients
c^G_i per Defs 2.19–2.21 computed INDEPENDENTLY (fresh implementation
generalizing `tr3s1_check.py`'s GMN side from e₀ = 1 to all e₀), with the
NORMALIZED Bézout representative 0 ≤ ℓ₀ < e₀ (ℓ₀h₀ ≡ 1 mod e₀) — the
project's standing GMN-convention hypothesis (TR3-S1 S0), and v₂ = w₁ (the
Def-2.5 identity at order 2).  Note t₁(i) = (s₁(aᵢ) − ℓ₀uᵢ)/e₀ is genuinely
nontrivial here (ℓ₀ ≠ 0), unlike the TR3-S1 stratum.

**The law, confirmed at every probed instance (A3, 0/3,640 with per-slot
count 7,255).**  For every nonzero f, every on-line slot j:

    (TWIST-LAW)   C^F_j = z₁^{ℓ₀·g₀·h₀·s_j} · c^G_{s_j},

equivalently ratio(j+1) = ratio(j)·z₁^{ℓ₀g₀h₀e₁}.  Derivation (displayed in
the script header, fixed pre-run): the corrected ǫ₁(γ_j) = z₁^{ℓ′₀s−ℓ₀u},
the inner-read z-shift m₀ = (s₁(aᵢ) − s(γ_j))/e₀ (Lemma-A-general, A2), and
GMN's t₁-exponent combine via ℓ₀γ_j = s + e₀(ℓ₀u − ℓ′₀s) to the pure
z₁-character with exponent ℓ₀·g₀·h₀·s_j (w₁(Φ₁) = e₀g₀h₀).  At e₀ = 1 the
exponent dies (ℓ₀ = 0): TR3-S1's identity, re-verified as the A5 control.

**What this settles and does not.** GRB S3.4(ii) said "the conjectured
discrepancy is the corrected weight-driven unit ǫ threaded per slot, UNTESTED
against GMN".  It is now TESTED: the discrepancy is exactly the displayed
z₁-character — a pure abscissa-keyed twist, EXACTLY as the corrected-ǫ
threading yields, at 52 towers × ~70 f-shapes each.  The twist is genuinely
nontrivial off the stratum (A6: the naive FGMN = GMN identity fails at ALL
1,023 twist-visible slots), and the retired S3.2-artifact increment z₁^{γ₂}
is dead off-stratum too (A7: 293/293).  STATUS: TR-3′-GEN(ii) is upgraded
from "open, shape unknown" to **open with the exact closed form displayed
and instance-confirmed**; this is still a CONJECTURE at proof level — a
finite-algebra proof note in TR3-S1's format (same σ-identifications, now
with the ǫ/t-exponent bookkeeping above) is the natural next unit, and the
derivation in the script header is essentially its computation.  Any future
GD3-FULL/OL-B consumer of the (2′) R_λ leg at e₀ ≥ 2 must thread
z₁^{ℓ₀g₀h₀s_j}, not a per-argument constant: the twist varies slot-by-slot
(constant only in j-increments).

## S2. Family B — the D-ITER composite: cyclic presentation FALSE at the canonical alphabet; the true iterated law measured

**Object.** The degree-0 composite digit algebra of gr(w₂) at E₂ = e₀e₁ > 1,
probed through the FGMN graded representation (multiplicativity T3/T4 =
N-1-sealed), on CANONICAL ANCHORS — the iterated eq-(12-int) split
φ_γ = π^{u₁}Φ₀^{s₁}Φ₁^{s₂}, the composite analogue of D-REAL's basis and the
alphabet the digit map dig reads (IFACE(c)'s consumed object).  Values in
K₂ = K₁[z̄]/(ψ₁) via y ↦ z̄; cocycle c(γ,γ′) := val(φ_γφ_{γ′})/val(φ_{γ+γ′})
(gauge-free: same weight).  This is exactly the layer BEYOND T10 (which only
walked R₂(Φ₁^s), the last-read e₁-letter).

**The measured law (B2, 0/804 pairs, all 52 towers).**

    (ITER-LAW)   c(γ,γ′) = z̄^{δ₂} · z₁^{(s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀γ₂δ₂)/e₀},
                 δ₂ = ⌊(s₂(γ)+s₂(γ′))/e₁⌋.

Two independent structure constants: the OUTER carry contributes z̄ (the
last-read wrap, as in D-REAL), the INNER carry contributes z₁ (the frame's
letter), and the outer wrap FEEDS the inner track (the +ℓ₀γ₂δ₂ term: an
outer wrap dumps h₁ mod e₀ of abscissa into the s₁-coset — the genuine
fibration ℤ/E₂ of §F.2's "fibred by the old").  At e₀ = 1 this degenerates
to c = z̄^{δ₂}: Lemma D-REAL verbatim (B3 controls green, ζ′ = z̄ with the
s₂-relabeling).  At e₁ = 1 it degenerates to c = z₁^{δ₁}.

**The adjudication (B3-adj).**  The PROBED display — GRB S5.3's open D-ITER
presentation claim, "the composite is the cyclic algebra
F′[u′]/(u′^{e_b′} − ζ′)" with a SINGLE structure constant, operationalized
at the canonical alphabet (single non-1 cocycle value + carry pattern
realizable by some relabeling of ℤ/E₂) — is **FALSE at mixed stacked
ramification**: NOT-CYCLIC at 22 of the 28 towers with e₀ ≥ 2 AND e₁ ≥ 2,
with all bug-detector and sealed rows green.  Two failure genres, both
witnessed:
* **≥ 2 distinct non-1 cocycle values** — e.g. designed row N
  (2;2,1,1;2,1,2), where K₂ = K₁[z̄] is a genuine degree-2 extension so
  z̄ ∉ ⟨z₁⟩ is guaranteed: values {z₁, z̄, z̄z₁^b} — no single ζ′ exists.
  Likewise J, M (F₁₆/F₈₁-based), L.
* **single value but carry pattern unrealizable** — e.g. C/K/E over p = 3
  rings: the value set collapses (small field) to {1, z₁}, but the mixed
  δ₁/δ₂ pattern is not the carry pattern of ANY ℤ/E₂ relabeling.
The 6 CYCLIC mixed towers are exactly the twist-blind collapses (z₁ = z̄ = 1
or the two constants collide compatibly) — the same small-field blindness
the G2 lesson displayed, here on the composite side.

**Honesty display (what is NOT refuted).**  The ABSTRACT presentation
K₂[U]/(U^{E₂} − ζ*) is automatic for any crossed product of ℤ/E₂ by K₂*
(take the weight-1 letter as U; its holonomy ζ* is measured per tower as
ζ_w1 in the output, with ζ_key = z̄^{e₀}z₁^{ℓ₀γ₂-…} the key-class holonomy)
— that reading carries no risk and no information.  What the probe refutes
is the single-constant carry law AT THE CANONICAL (dig-consumed) ALPHABET —
the direct composite analogue of what D-REAL proves at E_i = 1 and the form
the §F.2 display suggests ("𝒟′ = F′[u′]/(u′^{e_b′} − ζ′)").  §F.2's own
hedge — "in general the twisted composite (𝒟 ⊗_F F′)[u_new]/(relation), the
iterated construction" — is CONFIRMED, with the relation now measured:
(ITER-LAW) above IS the relation.  MOVES pass-8 critical 3 ("the general
new-stage digit algebra is not defined") is hereby answered at order 2 by
measurement.

**Consequence for (H1)(a) / D-ITER.**  D-ITER should be RE-STATED: not "the
composite is cyclic with some ζ′" but "the graded anchor system realizes the
iterated twisted product with structure constants (ITER-LAW)" — a statement
now instance-true at 804/804 pairs and with a clear proof route (the same
CARRY-1/W-MULT bookkeeping that proved D-REAL, run in the fibred index).
Any Lean carry-algebra kernel or §F.2 consumer that would have baked in
`F'[u]/(u^{e_b'} − ζ')` for the composite stage MUST NOT: at stacked
ramification the canonical alphabet needs two constants and the fibration
term.  This is the re-route the Tier-3 charter priced — caught for the cost
of a numerics run, before any proof unit consumed the cyclic form.

## S3. Perimeter and statuses (the honest box)

* Instances, not proofs: both headline laws are confirmed at exact instances
  (order 2, E₂ ≤ 6, p ∈ {2,3}, four base rings, d₀ ≤ 2) — conjecture-level
  statements with displayed closed forms; deeper orders and the general
  proof are open.  The e₀ = 1 legs are theorem-backed (TR3-S1, D-REAL).
* The FGMN side rides N-1's transcription (its external pins T0/T11/P11/P12
  cover it); the GMN side of Family A is freshly implemented from the
  printed Defs; Family B rides the T3/T4-sealed representation — its
  decorrelated legs are the bug-detector rows and the CERT/PARI
  certification of the four new tower rows (344 samples, 0).
* The (CYC)-vs-(ITER-LAW) adjudication is basis-relative BY DESIGN: the
  canonical alphabet is the consumed one.  A different distinguished
  alphabet could be proposed; any such proposal now has 22 exact tables to
  match (JSON on file).
* Family A's law is stated for the harness's canonical Φ₂ (both operators
  read the SAME key development — the correct comparison; key-choice
  variance is TR-3′-GEN σ-freedom, not probed here).

## S4. Run record

`python3 strata_probe.py` → exit 0, 12.7s, 43,992 samples; violations 0 on
all preregistered rows; output + JSON committed alongside.  Seed 20260815;
reruns byte-identical.  PARI leg: cypari2 factorpadic/idealprimedec on the
16 ℤ_p instances of K/L/M/N inside CERT/T11 (unique prime above p, (e,f) =
(e₀e₁, d₀g₀g₁) — all exact).
