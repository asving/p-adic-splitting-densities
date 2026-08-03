# ITERLAW4_PROBE — sealed preregistration: the (ITER-LAW-n) recursion at n = 4 — c₄(γ,γ′) = z̄₄^{δ₄}·z₃^{D₃}·z₂^{D₂}·z₁^{D₁} on standard-lift 4-read towers, with the subwindow-restriction gate F-SUB run FIRST and the level-3 single-source legs (inflation-defect, INV-4 class, J-windows) promoted to sealed predictions

**Unit: WAVE-19 UNIT 1 = the convergence judge's S4 spec, executed exactly**
(charter = `lean/notes/openmath/L3CONVERGENCE_2026-08-08.md` S4: "ITERLAW4_PROBE —
the n = 4 confirmation of (ITER-LAW-n), Candidate 2 at its first unconfirmed
order"). PROBE-FIRST: the product is a MEASURED-LAW VERDICT on the n = 4
instance class, not a proof note; per the judge's S4 decision-default the
(ITER-LAW-3) compose/proof unit proceeds in parallel and this probe's role is
to catch a wrong uniformization before the induction is drafted at general r.
**Two-commit seal:** this file's S0–S4 + the runner
`verification/openmath/iterlaw4_probe.py` are committed BEFORE any battery run
(commit 1); the S5 verdict block + outputs land at commit 2. Design-phase
disclosure (pre-seal, per the strata3e2/iterlawr precedent): `py_compile`, an
AST undefined-name scan, and the runner's `--design` mode (tower construction +
constants + letter orders + mutation/LIFT-DEV design-time visibility + a
pmul/dev cost probe — NO law comparison, NO val₄ of any pair, NO measured
anchor value) were run pre-seal; their consequences are pinned in S2/S3 below.
Seed: **20260905** (fresh; never used in this genre — grep-verified). Author:
Fable, wave-19 unit 1, campaign date 2026-08-08 (wallclock 2026-08-03).

## S0. Authority, class pin, and the harness of record

**The accepted order-2 base (citation PASTED from the ledger defined-term
block, `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "ITER-LAW ACCEPTED —
2026-08-03"):** "Scope as accepted: the harness tower class (superset of
DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence restricted to E₂ > 1);
residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper
rides the accepted GRB retarget; orders ≥ 3 untouched." The order-2 theorem is
the ONLY proved rung. The level-3 rung consumed here is the sealed MEASURED law
(ITER-LAW-3) — instance-confirmed conjecture, zero violations on ≈133k samples
across the sealed run (seal 911431c) + m4 supplement + the five decorrelated
method notes; convergence judgment `L3CONVERGENCE_2026-08-08.md` S0–S2. Nothing
here consumes or upgrades either statement; on a GREEN verdict (ITER-LAW-4) is
a MEASURED LAW (instance-confirmed conjecture) and (ITER-LAW-n) gains its third
confirmed instance (n = 1 accepted, n = 2 measured, n = 3 measured) — nothing
more.

**Harness of record (consumed VERBATIM, no reimplementation).** The choice the
charter asks to cite: THE SEALED `iterlawr_probe.py` CALCULUS, not the
`level3_xcheck.py` from-notes reconstruction. Why: (i) the sealed calculus IS
the object the measured (ITER-LAW-3) was measured on, so the F0/F-SUB fidelity
legs tie the new level-4 layer to the exact apparatus of record — any defect in
the NEW layer shows against the sealed reference rather than being absorbed
into a fresh reconstruction; (ii) the decorrelated-reimplementation role is
already discharged six ways (L3CONVERGENCE S1 row 1: harness validity CONVERGED
6/6, incl. M5's matched-instance 4,224/4,224) — a confirmation probe should
extend the apparatus of record, not decorrelate from it; (iii) the one-level-up
mirror construction (Tower3 → Tower4) is the same discipline that produced the
sealed level-3 layer from the accepted level-2 layer, keeping the L6/L7
stacking provenance manifest. Consumed: `grb_order2_check.Tower` (levels 0–2,
canonical ε₁-corrected Φ₂), `strata3_probe.Tower3` (level-3 layer: eps2 reading
C, w3, R3w/R3s, realize2, canonical ε₂-corrected Φ₃ = build_Phi3, T5-analogue
key R3s(Φ₃) = ψ₂), `iterlawr_probe.Composite3` (the sealed level-3
anchors/cocycle/constants/law_value — the F0b and shadow reference),
`iterlawr_probe.closed_form2` (the accepted order-2 reference), and the
disclosed pick_irr3 shim (installed by importing iterlawr_probe, byte-untouched
sources).

**NEW in this unit (the only added calculus, the exact one-level-up mirror of
the Tower3 layer; `iterlaw4_probe.Tower4`/`Composite4`):** eps3(β) :=
z₃^{ℓ₂′s−ℓ₂u}, (s,u) = eq12(β,e₂,h₂) (Def 3.15 reading C at level 3, letter
z₃ = the K₃-generator over K₂); w₄(f) := min_j{e₃·w₃(a_j) + j·γ₄} over the
Φ₃-development; R₄w (Def 3.16 at i = 4: slot grid s₄ + je₃, slot weights
γ_j = (γ−s_jγ₄)/e₃, coefficient C_j = ε₃(γ_j)·R3v(a_{s_j}), R3v = the level-3
read evaluated at y ↦ z₃); realize3 (realize2 mirror) + Φ₄ = build_Phi4
(canonical ε₃-corrected lift; CERT-only — the cocycle does NOT consume Φ₄);
K₄ := K₃[z̄₄]/(ψ₃) via mk_field_ext; **val₄(f) := Σ_j R4w(f)_j·z̄₄^j ∈ K₄**; the
4-read canonical anchors and cocycle (below); ψ₃ picked by the shimmed
pick_irr3 over K₃ at idx = (h₁+h₂) mod 2 (the Tower3 idx convention one level
up; disclosed).

**Class pin.** Standard-lift 4-read towers, canonical ε-corrected lifts at
EVERY level (Φ₂ ε₁-corrected, Φ₃ ε₂-corrected — the LIFT-DEV lesson made a
design pin, per the S4 spec): reads (e₀,h₀,ψ₀), (e₁,h₁,ψ₁), (e₂,h₂,ψ₂),
(e₃,h₃,ψ₃), gcd(eⱼ,hⱼ) = 1, ψⱼ monic irreducible with ψⱼ(0) ≠ 0;
E₄ := e₀e₁e₂e₃; normalized Bézout pairs (ℓⱼ,ℓⱼ′). The (ITER-LAW-LIFT) residual
propagates to every level; the probed class is pinned to the canonical lift
class (the LIFT-DEV secondary leg S3-LD measures exactly the lift-change
deviation at the new level).

**The level-4 anchor alphabet (the 4-fold iterated eq-(12-int) split).** For
γ ∈ ℤ:

    (s₄,u₄) := eq12(γ, e₃, h₃);      β₃(γ) := u₄ − s₄·w₃Φ₃   [γ = e₃β₃ + s₄γ₄]
    (s₃,u₃) := eq12(β₃, e₂, h₂);     β₂(γ) := u₃ − s₃·w₂Φ₂
    (s₂,u₂) := eq12(β₂, e₁, h₁);     β₁(γ) := u₂ − s₂·w₁Φ₁
    (s₁,u₁) := eq12(β₁, e₀, h₀).

Anchor φ_γ := π^{u₁}·Φ₀^{s₁}·Φ₁^{s₂}·Φ₂^{s₃}·Φ₃^{s₄}; window W₄ = {u₁ ≥ 0};
probe windows W1 = [Γ₀, Γ₀+E₄), W2 = W1+E₄, W3 = W1+7E₄, Γ₀ ≡ 0 (mod E₄) fixed
by the deterministic design-time scan (u₁ ≥ 0 verified through 3·(Γ₀+8E₄)+2,
covering all pair and triple sums). Sanity (symbolic leg): w₄(φ_γ) = γ;
φ_{γ+E₄} = π·φ_γ. Cocycle:

    c₄(γ,γ′) := val₄(φ_γ·φ_{γ′}) / val₄(φ_{γ+γ′}).

## S1. THE CANDIDATE LAW (sealed; every constant named)

**(ITER-LAW-4) [THE PRIMARY CANDIDATE] = the (ITER-LAW-n) recursion of
ITERLAWR_PROBE S6 item 1 / L3CONVERGENCE S2 Candidate 2, unrolled at n = 4.**
For all γ, γ′ ∈ W₄, with all splits ITERATED as in S0 and
s_j-defect := s_j(γ)+s_j(γ′)−s_j(γ+γ′):

    c₄(γ,γ′) = z̄₄^{δ₄} · z₃^{D₃} · z₂^{D₂} · z₁^{D₁}

    δ₄ := ⌊(s₄(γ)+s₄(γ′))/e₃⌋ ∈ {0,1}                    [top carry]
    S₃ := δ₄·γ₄                                          [top shift]
    D₃ := (s₃-defect + ℓ₂·S₃)/e₂ ∈ ℤ                     [new middle exponent]
    S₂ := D₃·γ₃ + S₃·(ℓ₂′ − ℓ₂·w₂Φ₂)                     [composed shift, rung 2]
    D₂ := (s₂-defect + ℓ₁·S₂)/e₁ ∈ ℤ                     [middle exponent]
    S₁ := D₂·γ₂ + S₂·(ℓ₁′ − ℓ₁·w₁Φ₁)                     [composed shift, rung 1]
    D₁ := (s₁-defect + ℓ₀·S₁)/e₀ ∈ ℤ                     [inner exponent]

where z̄₄/z₃/z₂/z₁ are the level-4/3/2/1 letters (K₄ = K₃[z̄₄]/(ψ₃),
K₃ = K₂[z₃]/(ψ₂), K₂ = K₁[z₂]/(ψ₁), K₁ = K₀[z₁]/(ψ₀)), γ₂ = e₁w₁Φ₁+h₁,
γ₃ = e₂w₂Φ₂+h₂, γ₄ = e₃w₃Φ₃+h₃, w₁Φ₁ = e₀g₀h₀, w₂Φ₂ = e₁g₁γ₂, w₃Φ₃ = e₂g₂γ₃.
At e₃ = 1 (δ₄ ≡ 0, S₃ = 0, D₃ = the plain carry) the display collapses
VERBATIM to the measured (ITER-LAW-3) constants (δ₃, D₂, Σ, D₁) of the
subtower; at e₃ = e₂ = 1 to the ACCEPTED order-2 law. This is the n = 4
instantiation of the uniform recursion — one Bézout kernel per level, each
denominator e_{j−1} cured by its own level's composed correction ℓ_{j−1}S_j,
NO cross-level denominators.

**Provenance (displayed so a failure localizes; "L7 stacked on L7 stacked on
L7").** The Φ₃-development digit of the anchor product
P = π^UΦ₀^{S₁}Φ₁^{S₂}Φ₂^{S₃}Φ₃^{S₄} is a LEVEL-3 anchor pair product, so:
L6-4 (anchor value): val₄(φ_γ) = ε₃(β₃)·ε₂(β₂)·ε₁(β₁) — the ε-chain, one slot
one digit per level. L7-4 (pair value): val₄(φ_γφ_{γ′}) =
z̄₄^{δ₄}·ε₃(β₃+β₃′)·z₃^{δ₃ᶜ}·z₂^{δ₂ᶜ}·z₁^{δ₁ᶜ}·ε₂(β₂+β₂′)·ε₁(β₁+β₁′), with the
PLAIN carries δ₃ᶜ := ⌊(s₃+s₃′)/e₂⌋, δ₂ᶜ := ⌊(s₂+s₂′)/e₁⌋,
δ₁ᶜ := ⌊(s₁+s₁′)/e₀⌋ — the inner factors are the level-3 L7-3 verbatim on the
digit; the top slot shift z̄₄^{δ₄} is Case-I slot-grid absorption one more
level up. Equivalent W-MULT-4 form: val₄(φ_γφ_{γ′}) =
z̄₄^{δ₄}·val₄(φ_γ)·val₄(φ_{γ′}). Integer layer: β₃(γ+γ′) = β₃+β₃′+δ₄γ₄ (L1 at
(e₃,h₃)); β₂(γ+γ′) = β₂+β₂′+S₂ and β₁(γ+γ′) = β₁+β₁′+S₁ (the composed-shift
identities, G8); generalized EXP at each rung divides L7-4 by L6-4 at γ+γ′ to
yield the display.

**THE DISTINGUISHED ALTERNATIVE (ALT, sealed) — the "level-3-naive" template
of the S4 spec, the exact analogue of the level-3 cycle's separation pair (one
knob):** same δ₄, same D₃, but the NEW level's composed shift replaced by the
naive per-level composition S₂ⁿ := γ₃·δ₃ᶜ, recursion continued downward:
D₂ⁿ := (s₂-defect + ℓ₁S₂ⁿ)/e₁, S₁ⁿ := D₂ⁿγ₂ + S₂ⁿ(ℓ₁′−ℓ₁w₁Φ₁),
D₁ⁿ := (s₁-defect + ℓ₀S₁ⁿ)/e₀. The two coincide identically at δ₄ = 0 (there
D₃ = δ₃ᶜ and S₂ = γ₃δ₃ᶜ) and differ generically at δ₄ = 1. The probe measures
BOTH; ALT violation/separation counts are RECORDED (meters MSEP4i/MSEP4f +
the master-switch fence MSEP0), never part of the primary prediction. If the
primary fails where ALT holds, ALT becomes the finding; if both hold
everywhere the verdict says so honestly.

**What would falsify (ITER-LAW-4) — the explicit list (the S1 falsifier
taxonomy one level up + the judge's S2 structural falsifiers):**
1. Wrong z̄₄-power: top-slot shift ≠ δ₄ = ⌊(s₄+s₄′)/e₃⌋ (wrong modulus, > 1, or
   weight-dependent) — G2 shape clause; mutation m4.
2. Wrong new-level fibration: D₃'s ℓ₂γ₄δ₄ term wrong (absent/sign/ℓ₂′-for-ℓ₂/
   γ₃-for-γ₄) — G3/G4 at δ₄ = 1; mutation m1.
3. Wrong composed shift at the new level: S₂ ≠ D₃γ₃ + S₃(ℓ₂′−ℓ₂w₂Φ₂) — in
   particular ALT's γ₃δ₃ᶜ — G3 at δ₄ = 1, G8 unconditionally; mutation m2.
4. Wrong denominator at any rung (e₂/e₁/e₀ swapped or crossed) — G4
   non-integrality, the G8 phantom counter; mutation m3.
5. Missing twist unit ε₃ in the anchor value — G1 on ℓ₂ ≠ 0 rows with z₃ ≠ 1;
   mutation m5.
6. Subwindow-restriction failure: c₄ on (e₃ℤ)² ≠ embed(measured c₃) — F-SUB
   (the strongest structural leg, run FIRST).
7. Inflation-defect failure: deviation from the measured level-3 shadow not of
   the form z₃^{D₃−δ₃ˢ}z₂^{D₂−D₂ˢ}z₁^{D₁−D₁ˢ}, or present at δ₄ = 0, or
   carrying a z̄₄ component — F-INF/FINF0.
8. Class failure: κ_ℤ(δ₄-table) ≠ (E₄/e₃)ℓ₃ or class(c₄) ≠ INV-4 mod M^{E₄} —
   F-CLASS.
9. J-window failure at any rung; cocycle-identity/swap/descent failure; a
   cross-level denominator event; a g₃-dependence of the integer tables
   (FROZEN).
10. Cascade strata: failures localized at the new middle Case-II stratum
    (g₂ = 1 ∧ δ₃ᶜ = 1, where the Φ₃-development needs the canonical-lift
    reduction) or the stacked double/triple-cascade strata — coverage metered
    (MC-3/MC-2/MC-1/MC-TRP).

A FAILURE IS A FULL SUCCESS OF THE PROBE: any surviving law-RED is reported
with the exact violating tuple (tower; γ, γ′; measured; predicted; constants)
as the headline. No post-hoc candidate edits inside this seal; a revised
candidate = one new sealed prereg cycle at most, clearly bracketed.

## S2. Tower roster (all fresh; none is a roster row of any prior sealed unit)

(tag, d₀; e₀,h₀,g₀; e₁,h₁,g₁; e₂,h₂,g₂; e₃,h₃,g₃) over all four rings
{ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]} = 72 towers. Charter coverage (the S4 spec):
E₄ ∈ {8,12,16} exhaustive full W1×W1 blocks (note: E₄ ∈ {8,12} forces one
e_j = 1 — four reads ≥ 2 give E₄ ≥ 16 — so those rows double as the per-level
controls); the E₄ = 16 all-letters row (Q); per-level e_j = 1 controls
(C0–C3); stacked e₀ ≥ 2 rows (A4, B4, D2, + all E₄ = 16 rows); mixed-e rows
(B4, D1, D2, T, MUA, MUB); an E₄ = 16 row with g₃ = 2 and letters (P, R, Q);
one E₄ ≥ 24 stretch row (T); MIXED translate blocks in the FIRST battery (G7).

| row | data | E₄ | design point |
|---|---|---|---|
| A4 | (1; 2,1,1; 2,1,1; 2,1,1; 2,1,1) | 16 | fully stacked; triple-cascade live; FROZEN ref |
| P  | (1; 2,1,1; 2,1,1; 2,1,1; 2,1,2) | 16 | g₃=2: z̄₄ genuine; FROZEN pair with A4 (g_top only) |
| Q  | (1; 2,1,2; 2,1,2; 2,1,2; 2,1,2) | 16 | ALL LETTERS live (M2-S8 flag row: top-carry image vs M^{E₄}) |
| R  | (1; 2,3,1; 2,3,1; 2,3,1; 2,3,2) | 16 | h-track: all hⱼ=3, g₃=2 |
| S  | (2; 2,1,1; 2,1,1; 2,1,1; 2,1,1) | 16 | d₀=2 base inertia |
| B4 | (1; 3,2,1; 1,1,2; 2,1,1; 2,1,1) | 12 | e₀=3 stacked (ℓ₀=2), DEAD MIDDLE e₁=1: S-chain passthrough S₁=S₂ |
| D1 | (1; 2,1,1; 1,1,2; 3,1,1; 2,1,1) | 12 | e₁=1, e₂=3 mixed |
| D2 | (1; 3,2,1; 2,1,1; 1,1,2; 2,1,1) | 12 | e₂=1 (S₂=S₃ passthrough), stacked e₀=3 |
| C0 | (1; 1,1,2; 2,1,1; 2,1,1; 2,1,1) | 8 | e₀=1 CONTROL: D₁≡0, c₄ = z̄₄^{δ₄}z₃^{D₃}z₂^{D₂} |
| C1 | (1; 2,1,1; 1,1,2; 2,1,1; 2,1,1) | 8 | e₁=1 CONTROL: D₂≡0, S₁=S₂; c₄ = z̄₄^{δ₄}z₃^{D₃}z₁^{D₁} |
| C2 | (1; 2,1,1; 2,1,1; 1,1,2; 2,1,1) | 8 | e₂=1 CONTROL: D₃≡0, S₂=δ₄γ₄; c₄ = the (ITER-LAW-3) FORM with γ₃↦γ₄ |
| C3 | (1; 2,1,1; 2,1,1; 2,1,1; 1,1,2) | 8 | e₃=1 CONTROL: measured (ITER-LAW-3) TWO WAYS (M3-S3 style) |
| T  | (1; 2,1,1; 2,1,1; 2,1,1; 3,2,1) | 24 | STRETCH: e₃=3,h₃=2 deep top track; REDUCED legs |
| MUA| (1; 1,1,2; 2,1,2; 3,1,2; 2,1,2) | 12 | MUTATION row: ALL gⱼ=2 (every letter live), e₁≠e₂, e₂≠e₃ |
| MUB| (1; 1,1,2; 3,2,2; 2,1,2; 3,1,2) | 18 | MUTATION row: ALL gⱼ=2, flipped inequalities e₁>e₂<e₃, h₁=2 |
| LD1| (1; 1,1,1; 2,1,2; 2,1,1; 2,1,1) | 8 | LIFT-DEV dev row: g₂=1, z₂ live (g₁=2) |
| LD2| (1; 1,1,1; 2,1,2; 2,3,1; 2,1,1) | 8 | LIFT-DEV dev row: h₂=3 variant (visibility hedge) |
| LD3| (1; 1,1,1; 2,1,2; 2,1,2; 2,1,1) | 8 | LIFT-DEV INVARIANCE row: g₂=2 |

ψ₀, ψ₁ by the Tower's deterministic pick_irreducible (verbatim); ψ₂ by
Tower3's pick_irr3 through the disclosed iterlawr shim; ψ₃ by the same
shimmed pick_irr3 over K₃ at idx = (h₁+h₂) mod 2. All g₃ ≤ 2. Design-phase
dry run (pre-seal, disclosed): all 72 towers construct; window bases per the
`--design` table (e.g. A4: 192, Q: 800, MUB: 2736, T: 408); letter orders per
the design table (e.g. Zp,p=3,MUA: ord(z̄₄,z₃,z₂,z₁) = (3281,41,5,8); the two
A4-shape p=2 instances are field-blind — integer legs carry them, the
level-3 FULL8 precedent).

**Design-phase consequences pinned pre-seal (disclosed):**
* **REDUCED legs** (W1×W1 block only; G1 on W1; no G5/G7/GSWAP; every
  per-pair leg incl. F-SUB/F0/F-INF/F-J and F-CLASS still runs): row T on all
  rings, and rows Q, MUA, MUB on the two F_p[[t]] rings — fixed from the
  disclosed cost probe (Fpt core op 0.6–0.9 s on MUB, 40–75 ms on Q; ℤ_p
  cheap). Zp instances of Q/MUA/MUB run the FULL leg set.
* **Mutation design-time visibility (the m4 lesson institutionalized —
  verified BEFORE sealing, predictions only):** on the mutation battery
  (MUA/MUB × {ℤ₃, F₂[[t]]}) every one of m1–m6 is integer-divergent AND
  field-visible on EVERY battery row (m1 36/36 … m6 216/216 per the design
  transcript) — no mutation rides an invisible letter.
* **LIFT-DEV visibility:** ε₂(γ₃) ≠ 1 on LD2 in all four rings and on LD1 at
  p = 3 (LD1 at p = 2 has ε₂(γ₃) = 1: the identity is still sealed there,
  predicting plain ≡ canonical); δ₃ᶜ = 1 pairs present (16 per LD block).
* **CERT4P caps:** PARI factorpadic at degΦ₄ ≤ 64 and p-maximal nfinit at
  degΦ₄ ≤ 32 — Q (256), MUA (192), MUB (288) are PREREGISTERED DEFERRALS
  (counted, reported); all other ℤ_p rows run both legs. Honest deferral: no
  PARI analogue on F_p[[t]] (as always).

## S3. Preregistered falsifier legs and predictions (violation counts; law-RED = obs ≠ 0 on a LAW family)

ORDER OF EXECUTION per tower: **F-SUB FIRST** (the M4-R1 gate, law-free
measured-vs-measured), then F0a/F0b, then the G/F legs. LAW families
(predicted 0, all part of the LAW verdict):

FSUB  SUBWINDOW GATE: for all W1×W1 pairs with e₃|γ, e₃|γ′ (⟺ s₄ = 0):
      c₄(γ,γ′) == K₄-embed(MEASURED c₃(γ/e₃, γ′/e₃)) of the level-3 subtower
      (sealed Composite3), on the nose.                       PREDICTED: 0.
F0a   LEVEL-2 FIDELITY: the ACCEPTED order-2 closed form on the level-2
      subtower (SP.Composite + closed_form2), own W×W block, all 72 towers.
      RED here ⟹ HARNESS suspect, not the law.                PREDICTED: 0.
F0b   LEVEL-3 FIDELITY: the measured (ITER-LAW-3) reproduced on the level-3
      subtower — sealed Composite3 cocycle == sealed law_value (primary), own
      W×W block, all 72 towers. RED ⟹ HARNESS suspect.        PREDICTED: 0.
G1    L6-4 ANCHOR-VAL: val₄(φ_γ) == embed(ε₃(β₃)·ε₂(β₂)·ε₁(β₁)) ≠ 0, every
      letter of W1,W2,W3 (W1 only on reduced rows).           PREDICTED: 0.
G2    L7-4 PAIR-VAL, blocks W1×W1, W3×W3, W1×W3 (W1×W1 on reduced), BOTH
      forms: (a) z̄₄^{δ₄}·z₃^{δ₃ᶜ}·z₂^{δ₂ᶜ}·z₁^{δ₁ᶜ}·embed(ε₃(β₃+β₃′)·
      ε₂(β₂+β₂′)·ε₁(β₁+β₁′)); (b) z̄₄^{δ₄}·val₄(φ)·val₄(φ′) [W-MULT-4]; plus
      the shape clause: SINGLE nonzero top slot, at slot δ₄, weight γ+γ′.
                                                              PREDICTED: 0.
G3    THE CANDIDATE (ITER-LAW-4): measured c₄ == the S1 primary closed form,
      same blocks. ALT compared per pair (ALTDIFF/ALTVIOL recorded, not
      primary).                                               PREDICTED: 0.
G4    Per-level integrality warrants: e₂ | (s₃-def + ℓ₂S₃), e₁ | (s₂-def +
      ℓ₁S₂), e₀ | (s₁-def + ℓ₀S₁), all block pairs.           PREDICTED: 0.
G5    Cocycle identity: 216 sampled W1-triples (measured AND closed form,
      raw window sums) + 216 sampled QUOTIENT triples on the descended
      ℤ/E₄ table (the M2 window-AND-quotient point). Non-reduced rows.
                                                              PREDICTED: 0.
GSWAP Swap symmetry c₄(r,s) = c₄(s,r) on the W1 table (non-reduced).
                                                              PREDICTED: 0.
G6    Degeneration displays on every e_j = 1 rung: e₀=1 ⟹ D₁ = 0; e₁=1 ⟹
      D₂ = 0 ∧ S₁ = S₂; e₂=1 ⟹ D₃ = 0 ∧ S₂ = S₃ (+ on C2: D₂ equals the
      (ITER-LAW-3) FORM with γ₃ ↦ γ₄, the "measured level-3 law recovered as
      a form" clause); e₃=1 (C3) ⟹ THE TWO-WAY TIE, M3-S3 style: (way 1,
      split-chain verbatim) δ₄ = 0 ∧ (D₃,D₂,D₁) == the sealed level-3
      constants (δ₃,D₂,D₁) of the SAME pair; (way 2, value tie) c₄(γ,γ′) ==
      K₄-embed(measured c₃(γ,γ′)).                            PREDICTED: 0.
G7    ℤ/E₄ descent incl. MIXED blocks (COR-4 lesson, FIRST battery): W2×W2,
      W3×W3 == W1×W1 entrywise AND all four mixed blocks W2×W1, W1×W2,
      W3×W1, W1×W3 equal it entrywise. Non-reduced rows.      PREDICTED: 0.
G8    Integer layer, 20,000 symbolic draws (pure ℤ; eⱼ ≤ 12, hⱼ ≤ 39,
      gⱼ ≤ 4): L1 at all four levels; INNER-SHIFT-4 (β₃″ = β₃+β₃′+δ₄γ₄); the
      TWO composed-shift identities (β₂″ = β₂+β₂′+S₂, β₁″ = β₁+β₁′+S₁);
      D₃/D₂/D₁ integrality; generalized EXP at rungs 3/2/1; the symbolic
      J-windows; NO-cross-level-denominator phantom counter (draws where a
      failed e_{j−1}-divisibility would be rescued by e_{j−1}e_{j−2}) = 0.
                                                              PREDICTED: 0.
MSEP0 Master-switch fence (M3): every primary-vs-ALT separation pair has
      δ₄ = 1 (the L1-analogue: separation = pure top-carry leakage).
                                                              PREDICTED: 0.
FINF  INFLATION-DEFECT IDENTITY (M4-R2 promoted, vs the MEASURED level-3
      shadow, every block pair): c₄(γ,γ′) == z̄₄^{δ₄} · embed(c₃(β₃,β₃′)) ·
      z₃^{D₃−δ₃ˢ} · z₂^{D₂−D₂ˢ} · z₁^{D₁−D₁ˢ}, where c₃(β₃,β₃′) is the
      sealed MEASURED level-3 cocycle at the shadow pair and (δ₃ˢ,D₂ˢ,D₁ˢ)
      its sealed (ITER-LAW-3) constants. The deviation is z̄₄-free BY THE
      IDENTITY'S SHAPE — the sealed content is that no z̄₄ correction beyond
      δ₄ exists.                                              PREDICTED: 0.
FINF0 First-deviation locus: shadow deviation tuple ≠ (0,0,0) at δ₄ = 0.
                                                              PREDICTED: 0.
FINFMISS Shadow window misses (β₃-pair outside the level-3 window).
                                                              PREDICTED: 0.
FJ3/FJ2/FJ1  J-WINDOWS (M3 S6-(J) promoted, exact display per rung): at rung
      j, D_j − δ_jᶜ ∈ {⌊ℓ_{j−1}S_j/e_{j−1}⌋, ⌈ℓ_{j−1}S_j/e_{j−1}⌉} on every
      pair (at S_j = 0 this forces D_j = δ_jᶜ; at rung 3, S₃ = δ₄γ₄ gives
      M3's two-value window {⌊ℓ₂γ₄/e₂⌋,⌈ℓ₂γ₄/e₂⌉} on δ₄ = 1 pairs; the
      floor/ceil selection is the b-phase, counted, not preregistered).
                                                              PREDICTED: 0.
FCLASSK κ_ℤ(δ₄-table) := Σ_{k<E₄} δ₄(Γ₀+k, Γ₀+1) == (E₄/e₃)·ℓ₃ exactly (M2
      S3 one level up), every tower.                          PREDICTED: 0.
FCLASSS INV-4 CLASS: σ := Π_{k<E₄} c₄(Γ₀+k, Γ₀+1) ≡ z̄₄^{(E₄/e₃)ℓ₃} ·
      z₃^{e₀e₁ℓ₂} · z₂^{e₀ℓ₁} · z₁^{ℓ₀} mod M^{E₄}, M = ⟨z̄₄,z₃,z₂,z₁⟩
      (membership via x^{m/gcd(m,E₄)} = 1, m = exponent of M from exact
      letter orders). Field-blind towers (M = 1) counted separately; the
      "top-carry image escapes M^{E₄}" flag (M2-S8) REPORTED per tower —
      expected nontrivial on Q-type rows, not preregistered.  PREDICTED: 0.
FROZEN g_top-invariance (M3 fence): the FULL integer tables (δ₄,D₃,D₂,D₁) of
      A4 and P (identical data except g₃) agree entrywise at matched W1
      offsets, per ring.                                      PREDICTED: 0.
CERT2 level-2 subtower certification: G.T1_T2 (nf=6), G.T5, G.T11 (PARI on
      ℤ_p), all 72 towers.                                    PREDICTED: 0.
CERT3 level-3 data cert (sealed cert3_internal transcribed): ψ₂ data, Φ₃
      monic/deg/weight/no-slot-below, R3s(Φ₃) == ψ₂ exact.    PREDICTED: 0.
CERT4 level-4 data cert (one level up): ψ₃ monic/irred/ψ₃(0)≠0/gcd(e₃,h₃)=1;
      Φ₄ monic, deg = e₃g₃·degΦ₃, w₄(Φ₄) = e₃g₃γ₄, no slot below weight,
      R4s(Φ₄) == ψ₃ EXACT (the V4 key check two levels up).   PREDICTED: 0.
CERT4P PARI (ℤ_p, caps per S2): Φ₄ irreducible over ℚ_p; one prime,
      (e,f) = (E₄, d₀g₀g₁g₂g₃).                               PREDICTED: 0.

METERS (teeth/coverage; CONTROL verdict, sealed MATCH conditions):
  MD4    δ₄ = 1 pairs > 0 on every e₃ ≥ 2 row (each ring).
  MC-3   g₂ = 1 ∧ δ₃ᶜ = 1 (the NEW middle Case-II stratum) > 0 on A4,P,S,T.
  MC-2   g₁ = 1 ∧ δ₂ᶜ = 1 > 0 on A4,P,S,T.   MC-1  g₀ = 1 ∧ δ₁ᶜ = 1 on same.
  MC-TRP all three simultaneously > 0 on A4.
  MV     predicted c₄ ≠ 1 > 0 on P,Q,R,MUA,MUB (each ring).
  MSEP4i G8 draws with S₂ ≠ γ₃δ₃ᶜ > 0.  MSEP4f field-level separation count
         REPORTED (0 ⟹ honesty display, not RED).  LDVIS LIFT-DEV factor ≠ 1
         on ≥ 1 pair (per the design-visibility pin).

MUTATION CONTROLS (post-battery, same seal; battery = MUA/MUB over
(ℤ₃, F₂[[t]]), W1×W1 + anchors; every mutation of the closed form must be
detected at FIELD level (≥ 1 mismatch vs the MEASURED cocycle; non-integrality
counts) AND at WARRANT level (≥ 1 integer divergence/integrality loss — the
M4-S10 lesson); m4 additionally carries the STRUCTURAL top-slot leg (measured
top slot ≠ mutated δ₄ — fires even at z̄₄ = 1); undetected ⟹ verdict PARTIAL
(teeth), by construction never law-RED):
  m1 drop ℓ₂γ₄δ₄ from D₃ (chain recomputed)                 PREDICTED: detected.
  m2 S₂ → γ₃δ₃ᶜ (THE ALT as a mutation)                     PREDICTED: detected.
  m3 D₃ denominator e₂ → e₁ (teeth: e₁ ≠ e₂ on both rows)   PREDICTED: detected.
  m4 δ₄ → ⌊(s₄+s₄′)/e₂⌋ (wrong modulus; teeth: e₂ ≠ e₃, g₃ = 2 on both rows)
     + structural top-slot leg                              PREDICTED: detected.
  m5 drop ε₃ from the G1 anchor prediction                  PREDICTED: detected.
  m6 letter swap z₃ ↔ z₂                                    PREDICTED: detected.

SECONDARY SEALED LEG (LIFT-DEV-4; own verdict line, conjecture-grade — a
failure is a SECONDARY finding, not a law-RED): plain-Φ₃ twin towers (the
notes' standard-lift LIFT recursion, disclosed transcription; Φ₂ stays
canonical) on LD1/LD2/LD3 × all rings, W1×W1:
  LDDEV (g₂ = 1 rows): c₄^plain(γ,γ′) == c₄^canon(γ,γ′) · ε₂(γ₃)^{δ₃ᶜ} —
        the LIFT-DEV-3 factor ε₁(γ₂)^{δ₂} one level up; the gauge mechanism's
        genuinely new quantitative prediction (L3CONVERGENCE S4), previously
        unmeasured.                                          PREDICTED: 0.
  LDINV (g₂ = 2 row): c₄^plain == c₄^canon identically (invariance at
        g₂ ≥ 2, mirroring LIFT-DEV-3's g₁ ≥ 2 invariance).   PREDICTED: 0.
  LDCERT plain-Φ₃ sanity (monic, deg, w₃ = e₂g₂γ₃; NOT the R3s key — the
        canonical correction is exactly what the plain lift lacks).
                                                             PREDICTED: 0.

DISCIPLINE: exceptions are HARNESS EVENTS, recorded per tower, classified
before any law verdict; CERT/F0/F-SUB rows are bug detectors first. THE THREE
VERDICT LINES (pre-agreed wording, the RED-line lesson): "LAW VERDICT
(ITER-LAW-4 primary, predicted-0 families)" counts ONLY the LAW families
above; "CONTROL VERDICT (meters + mutation teeth)" = MET or PARTIAL(teeth)
with the failing controls listed; "SECONDARY VERDICT (LIFT-DEV-4)" separate.
A control failure NEVER prints as a law failure. Exit 0 iff all three clean.
DETERMINISTIC: random.seed(20260905), exact arithmetic only. JSON:
iterlaw4_probe_results.json; transcript: iterlaw4_probe_output.txt.

## S4. What this probe does NOT claim (fences)

* No proof: a GREEN verdict makes (ITER-LAW-4) a MEASURED LAW and (ITER-LAW-n)
  a three-instance-confirmed uniform conjecture — the compose/proof unit is
  the parallel wave-19 lane (L6-(n)+W-MULT-(n) per L3CONVERGENCE S3); numerics
  falsify, never prove.
* No orders ≥ 5 claim; no general-lift claim ((ITER-LAW-LIFT) propagates,
  LD legs measure only the specific ε₂(γ₃)^{δ₃ᶜ} deviation on the specific
  plain lift); no gr(w₄) semantics claim; no GMN-side claim (battery is
  FGMN-calculus-internal).
* The (INV-n) class and J-window legs test the M2/M3 SINGLE-SOURCE cells at
  n = 4; they do not upgrade the n = 3 single-source status (that needs a
  second method at n = 3, or the compose unit).
* No edits to any accepted or sealed record; ITERLAW / ITERLAWR_PROBE /
  L3CONVERGENCE / the five method notes / all sealed runners byte-untouched
  (the iterlawr pick_irr3 shim is runtime monkey-patching, disclosed there and
  reused here).
* CERT4P deferrals on Q/MUA/MUB (degree caps) are preregistered honest
  deferrals; their internal CERT4 (R4s(Φ₄) = ψ₃) still runs.

## S5. VERDICT (post-run; commit 2 fills this block — PENDING at the seal)

PENDING.
