# Verdict: MH.11 — Theorem B (`dv_oneSlope_split_unique`, F1.H2)

**Status: LANDED, unconditional, zero `sorry`, zero carried hypotheses, Lean-core axiom
footprint.**

## What was asked

Prove Theorem B (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §2 "Theorem B (uniqueness —
F1.H2, completeness-free, Newton-free)", proof plan §5, node MH.11 of the §9 table, plan row
F1.H2) in a new file `leanfinal/Uniformity/ChapC/C133mh11.lean`, consuming the landed Hensel
engine root (C133mh3's Theorem M) — mechanism: M-forced exponent match + degree pigeonhole,
NO filtration induction.

## What landed

File: `leanfinal/Uniformity/ChapC/C133mh11.lean` (new; 322 lines; namespace
`Uniformity.Density.Tower.C133mh11`; imports `C133mh3`, `C133mh10`, `C35`).

**Headline (public):** `dv_oneSlope_split_unique` — the §2 statement verbatim:

* §1 pack as `L : LevelDatum F H₀ hpin` (C.09; `L.hκ` IS the strict floor
  `ℓ·(D′·F.h) < u` up to `mul_assoc`) + `hπ : Irreducible π` + `hh : 0 < F.h`.
  **No completeness anywhere** (no `IsAdicComplete` in the file).
* `g` with `IsDvPure F g L.u L.ℓ` and `(F.e₁*F.f₁) ∣ g.natDegree`; splits
  `hab : g = a * b`, `hab' : g = a' * b'`; `a, b, a', b'` all `Monic`;
  `a, a'` additionally `IsDvPure`.
* Exact residuals in the ∃-pin (`HasLabel`-shaped, C.29) form with explicit exponents:
  `∃ hne M₀ hp, dvResPoly F H₀ hpin a L.u L.ℓ hne M₀ hp = L.r ^ m` (and `m'` for `a'`),
  with `hm : 0 < m`, `hm' : 0 < m'` (§2's fences, carried verbatim; the proof happens to
  close without them — recorded in the file header, statement kept faithful).
* Complements in the ∀-pin form, byte-parallel to the signed C.34 complement clause (the
  conclusion shape of `block_pair_self_of_dvResPoly_eq_pow`):
  `∀ hne M₀ hp, ¬ L.r ∣ dvResPoly F H₀ hpin b L.u L.ℓ hne M₀ hp` (and for `b'`).
* Conclusion: `a' = a ∧ b' = b`.

NOT assumed, all derived (per §2's "Note what is NOT assumed"): purity of `b, b'`, degrees
of `a', b'`, any relation between `m` and `m'`. `g.Monic` is also not a hypothesis
(derivable from `hab`/`ha`/`hb`; recorded in the header's statement-fence notes).

**Private helpers** (all in-file, all proved):

* `exists_pin` — nonzero ⟹ full side pin (C.34 `dvSideSet_nonempty` + `DvOnSide`
  finiteness at `Finset.min'_mem`).
* `dvResPoly_pin_congr` — C.25's junk-total pin irrelevance across a polynomial equality
  (numeral forced by `ENat` coe-injectivity, the rest by proof irrelevance; `subst`+`rfl`).
* `linear_pigeon` — the summed-slack pigeonhole `P ≤ A → Q ≤ B → P + Q = A + B → P = A`
  (`omega`); this replaces §5(B1)'s floor-division case analysis entirely.
* `mul_sideMax_degree_pin` — **(B1) defect-vanishing**: in a monic split `x·y` of a
  `D′`-divisible-degree pure product, purity of `x` forces `D′·(deg x/D′) = deg x`.
  Inputs: `C133mh3.dvSideMax_mul` (MH.2), `dvSideMax_eq_of_isDvPure` +
  `le_natDegree_div_of_mem_dvSideSet` (the landed C.35 caps), `Monic.natDegree_mul`,
  `Nat.mul_div_cancel'`.
* `natDegree_of_pure_pow` — the exact degree read `deg x = D′·(ℓ·(m·d_r))` from
  `natDegree_div_eq_of_isDvPure` (C.35) + `natDegree_dvResPoly` (the C.26 degree law) +
  `Monic.natDegree_pow`.
* `isKey_X`/`localFieldStageField` — the standing private D9 field reconstruction
  (C.04/C.12/C.26/C.47/C133mh3 convention; C.04 exports no instance).

## Proof route (= §5, made precise)

* **(B2)** `C133mh3.dvResPoly_mul_gen` (MH.3, τ = 1) on both splits at `exists_pin` pins;
  the two product residuals matched through `dvResPoly_pin_congr (a*b = a'*b')`; then
  `C133mh10.dvResidualBezout_unique` (Theorem H0's uniqueness half, under the local field
  instance) with the ∀-pin complements as the `¬ r ∣ ·` legs gives `m = m'` directly —
  no separate UFD bookkeeping.
* **(B1)** run twice, once per split, via `mul_sideMax_degree_pin` (the second split's
  purity/divisibility hypotheses transported across `hab'` by `rw [← hab']`); composed
  with `natDegree_of_pure_pow` and `m = m'`: `deg a' = D′·ℓ·m·d_r = deg a`.
* **(B3)** `by_contra`: `δ := a' − a ≠ 0` forces `ε := b − b' ≠ 0` (monic cancellation);
  `a·ε = δ·b'` by `mul_sub/sub_mul/hab'`; M clause 3 on this single polynomial + pin
  congruence: `r^m·R(ε) = R(δ)·R(b')`; `(L.hrirr.coprime_iff_not_dvd.mpr …).pow_left` +
  `IsCoprime.dvd_of_dvd_mul_right` give `r^m ∣ R(δ)`, so `m·d_r ≤ deg R(δ) = sideDeg(δ)`
  (C.26 degree law + `natDegree_le_of_dvd`). Upper: `ℓ·sideDeg(δ) ≤ sideMax(δ)`
  (`dvSideLen_eq`, C.08) `≤ deg δ/D′` (C.35 cap), so `D′·ℓ·sideDeg(δ) ≤ deg δ < deg a =
  D′·ℓ·m·d_r` (`degree_sub_lt` on the equal-degree monics), cancel `D′` then `ℓ`
  (`Nat.lt_of_mul_lt_mul_left`): `sideDeg(δ) < m·d_r`. Contradiction; `b' = b` follows by
  `mul_left_cancel₀`.

## Verification

`cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C133mh11.lean`
— exit 0, output exactly one line (no warnings):

```
'Uniformity.Density.Tower.C133mh11.dv_oneSlope_split_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry` (grep-verified), zero new axioms, no cite inherited (the engine route never
touches `fgmn_dv_exact_mul`).

## Carried hypotheses / opens

None. Theorem B is unconditional given the landed inputs; every §5 step went through
against the landed operators. The only deviations from a literal §5 reading, all recorded
in the file header's "Statement-fence resolutions":

1. §5(B2)'s "unique r-adic valuation in the UFD" is discharged by the already-landed
   `C133mh10.dvResidualBezout_unique` instead of fresh UFD arithmetic.
2. §5(B1)'s floor-division remainder analysis (`r_a + r_b ∈ {0, D′}`) is replaced by the
   equivalent summed-slack pigeonhole (no case split); the conclusion (`D′ ∣ deg a'`,
   exact cap on the cofactor) is the same.
3. §5(B3)'s `τ₃, τ₄` units are identically 1 (MHFIX τ = 1 normalization, as landed in
   `dvResPoly_mul_gen`).
4. `hm, hm'` (§2's `m, m' ≥ 1`) turn out to be unconsumed by the proof; they are kept in
   the signature for statement fidelity (linter silenced on the one declaration).
