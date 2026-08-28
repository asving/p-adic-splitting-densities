# Verdict — UNIT MH13 (node MH.13, Theorem C: placement/maximality, degree-pinned)

**Target file:** `leanfinal/Uniformity/ChapC/C133mh13.lean` (new, 305 lines).
**Namespace:** `Uniformity.Density.Tower.C133mh13`.
**Verify command:** `cd leanfinal && lake env lean Uniformity/ChapC/C133mh13.lean` — GREEN,
zero `sorry`, zero warnings.

## Status: LANDED, UNCONDITIONAL — Theorem C is proved

Both public declarations print footprint EXACTLY
`[propext, Classical.choice, Quot.sound]` (AxCheck footer, verified in-file).
**No carried hypotheses** — every §6 input was already landed (MH.2/MH.3 in `C133mh3.lean`
unconditional, MH.12 in `C133mh12.lean`), so the C133mh3-conditional-layer pattern was not
needed. No new axiom, no statement weakening, no existing file edited, no imports of the
concurrent MH4/MH11 files.

## Per-clause table

| decl | doc source | status |
|---|---|---|
| `theoremC_placement` (★ public) | §2 "Theorem C (placement/maximality — the BlockFrontier clause, DEGREE-PINNED)": `f` monic, `Squarefree f`, `f = P*Q*W`; P monic pure `D′∣deg`, `R(P) = L.r^m` (`m ≥ 1`); Q monic pure `D′∣deg`, `L.r ∤ R(Q)`; W monic point-sided (`dvSideDeg = 0`); conclusion: `HasLabel L fS' ∧ D′ ∣ fS'.natDegree → fS' ∣ f → fS' ∣ P` | PROVED, unconditional |
| `dvSideDeg_ne_zero_and_r_dvd_of_factor` (★ public) | §6.2's per-prime bullet input ("`qᵢ` is not far … and `R(qᵢ) = τ'·r^{aᵢ}`, `aᵢ ≥ 1`"): a positive-degree monic factor `q` of a monic pure `D′`-divisible `q*w` with exact residual `L.r^m` has `dvSideDeg ≠ 0` AND `L.r ∣ R(q)` | PROVED, unconditional |
| `exists_monic_descent` (private) | §6.2 descent ¶ (Gauss descent packaging: irreducible over `K₀ = FractionRing O` dividing a monic image ⟹ monic positive-degree `O`-descendant dividing every `y` whose image `q₀` divides) | PROVED |
| `q_leg_false` / `w_leg_false` (private) | §6.2's "`qᵢ ∣ Q` ⟹ `r ∣ s` ✗" (τ=1 mixed law `C133mh3.dvResPoly_mul_gen` inside `Q = q'·wQ`) and "`qᵢ ∣ W` ⟹ `sideDeg(qᵢ) ≤ sideDeg(W) = 0` ✗" (`C133mh3.dvSideDeg_mul`) | PROVED |
| `exists_pin`, `dvOnSide_of_mem'`, `floor_assoc`, `isKey_X`, `localFieldStageField` (private) | plumbing: pin existence from C.07's `DvOnSide` finiteness guard; `LevelDatum.hκ` re-association; standing D9 conventions (copies of C133mh3/C133mh0 privates) | PROVED |

## Resolution record (per the brief's "resolve ambiguity against the signed A-C.20 shapes")

- **`HasLabel′` = signed A-C.20 competitor shape, verbatim**: the hypotheses
  `hlab : HasLabel L fS'` + `hpinned : (F.e₁ * F.f₁) ∣ fS'.natDegree` — byte-matched
  against `BlockFrontier`'s maximality quantifier (`C35.lean:280-282`) and C.34's pinned
  competitors (`C35.lean:169-171`). The pin is load-bearing (§7's refutation record).
- **"R(Q) = s with r ∤ s"** transcribed with `s := R(Q)` itself: `¬ L.r ∣ dvResPoly … Q …`.
- **Residual pins** (`hne₂, M₀, hpin₂` triples for P and Q) carried as theorem hypotheses in
  `HasLabel`'s own internal shape — no ∃/∀-pin ambiguity arises because the value of `M₀`
  is unique (`dvHgt` is a function into `ℕ∞`, `Nat.cast` injective) and the `hpin₂` proof
  argument is proof-irrelevant. MH11's `dvResPoly_pin_congr` was therefore not needed
  (and C133mh11 is not imported, per the concurrency fence).
- **`LevelDatum.hκ` associativity**: `ℓ * D′ * h < u` (C.09) vs the MH3/MH12 floor shape
  `ℓ * (D′ * h) < u` — bridged once (`floor_assoc`, `mul_assoc`).

## Honest consumption note (proof STRENGTHENS §6.2; statement unchanged)

The landed proof does NOT consume `Squarefree f`, the P-clauses
(`hPmon/hPpure/hPdeg/hpinP/hm/hPres`), `hQpure`, `hQdeg`, or `hf` — all carried verbatim
per the §2 statement fence (extra hypotheses never weaken the theorem; consumers get the
§2 interface they expect). Reason: instead of §6.2's squarefree `∏ᵢ qᵢ` distinct-prime
factorization, the assembly proves `IsCoprime (fS'.map) ((Q*W).map)` over
`K₀ = FractionRing O` (mathlib `isCoprime_of_dvd`, Bezout): ANY common irreducible `q₀`
Gauss-descends (MH12 `exists_monic_map_eq_of_dvd_map` + monic `Polynomial.map_dvd_map`)
to a monic `q' ∣ fS'` of positive degree; inside the pure PINNED `fS' = q'·wS`, MH12's
no-far-primes gives `dvSideDeg(q') ≠ 0` and the τ=1 mixed law + `dvd_prime_pow` in `K[Z]`
(stage field, `localFieldStageField`) gives `L.r ∣ R(q')`; `q₀` prime then forces
`q' ∣ Q` (kills `L.r ∤ R(Q)`) or `q' ∣ W` (kills the point side) — contradiction. Then
`IsCoprime.dvd_of_dvd_mul_right` + monic map-descent give `fS' ∣ P` with multiplicity
bookkeeping absorbed by coprimality. This strengthening is recorded in the file header;
if the owner prefers the letter of §6.2's squarefree route, the statement is already the
§2 one and nothing changes downstream.

## Named inputs consumed

`C133mh3.dvResPoly_mul_gen` (Theorem M clause 3, τ=1) · `C133mh3.dvSideDeg_mul` (clause 2)
· `C133mh12.not_dvSideDeg_eq_zero_of_isDvPure_mul_of_natDegree_pos` (no-far-primes) ·
`C133mh12.exists_monic_map_eq_of_dvd_map` (Gauss descent) · `natDegree_dvResPoly` (C.26)
· `dvSideSet_nonempty` (C.34) · mathlib: `isCoprime_of_dvd` (Bezout),
`WfDvdMonoid.exists_irreducible_factor`, `Irreducible.prime`, `dvd_prime_pow`,
`Polynomial.map_dvd_map`, `Polynomial.monic_mul_leadingCoeff_inv`,
`Polynomial.Monic.of_mul_monic_left`.

## Opens / follow-ups for MH.14 (frontier assembly, not this node)

- Sizing overrun: 305 lines vs the node table's 100–170 — the delta is the header
  resolution record plus the storm-forced staging into named private lemmas; no
  mathematical scope creep.
- `set_option linter.unusedVariables false` is file-local, solely for the §2-carried
  unconsumed hypotheses above.
- The §8 assembly (`BlockFrontier` from `BlockContext`, F1.H3's existence half) still
  needs Theorem A/B + X1 promotion; this node supplies exactly the `∀ fS'`-maximality
  clause: instantiate `theoremC_placement` and feed its conclusion to
  `blockFrontier_intro` (C35.lean:287) with the witness from the existence half.
