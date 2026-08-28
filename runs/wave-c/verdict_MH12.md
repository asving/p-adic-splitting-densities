# Verdict — UNIT MH12 (node MH.12, HENSEL_ENGINE_2026-08-26.md §9)

**Target file:** `leanfinal/Uniformity/ChapC/C133mh12.lean` (new, 216 lines).
**Namespace:** `Uniformity.Density.Tower.C133mh12`.
**Verify command:** `cd leanfinal && lake env lean Uniformity/ChapC/C133mh12.lean` — GREEN,
no `sorry`, no warnings.

## Status: LANDED, unconditional, feeds MH.13

All four public declarations compile with footprint EXACTLY
`[propext, Classical.choice, Quot.sound]` (AxCheck footer, verified in-file). Named input
consumed: **MH.2** (landed `C133mh3.dvSideMax_mul` / `dvSideMin_mul`, Theorem M clauses
1–2, UNCONDITIONAL) + mathlib (`Polynomial.isIntegral_coeff_of_dvd`,
`IsIntegrallyClosed.isIntegral_iff`, `Polynomial.lifts_and_degree_eq_and_monic`). No new
axiom, no carried hypothesis, no `sorry`.

## Per-lemma table

| decl | source (§6.1/§6.2) | status |
|---|---|---|
| `nat_defect_vanishing` (private) | pure ℕ arithmetic core underlying (B1)/§6.1 ¶1 | PROVED |
| `dvSideMax_tight_and_dvd_of_isDvPure_mul` | §6.1 ¶1, defect-vanishing (generalizes §5's (B1): `x=y·z` monic, `x` pure, `D′∣deg x` ⟹ both cofactors `D′`-divisible AND both `dvSideMax` tight to `natDegree/D′`) | PROVED, unconditional |
| `natDegree_eq_zero_of_isDvPure_mul_of_dvSideDeg_eq_zero` | §6.1 ¶2, no-far-primes (positive form: a point-sided factor of a pure `D′`-divisible product has degree 0) | PROVED, unconditional |
| `not_dvSideDeg_eq_zero_of_isDvPure_mul_of_natDegree_pos` | §6.1 ¶2, contradiction form ("q is a unit — contradiction") | PROVED, unconditional |
| `exists_monic_map_eq_of_dvd_map` | §6.2, Gauss descent (mathlib `IsIntegrallyClosed` search) | PROVED, unconditional |

## Design notes / faithfulness

- **Defect-vanishing generalized, not weakened.** The doc's §6.1 ¶1 prose reads "whenever
  `y` is pure, `D′ ∣ deg y` automatically, and `sideMax(z) = deg z/D′` exactly." The proof
  shows purity of `y` is never actually used — only purity of the PRODUCT `x = y·z` plus
  `D′ ∣ deg x`. The landed lemma states the fully symmetric (stronger) form: both cofactors
  get both conclusions. This is the literal (B1) argument of §5 (mixed-remainder squeeze),
  transcribed once and reused for both directions; nothing in the doc's statement is
  weakened, and the symmetric form implies the asymmetric one stated in the prose.
- **No-far-primes** matches §6.1 ¶2 exactly: `sideMin`-additivity (`C133mh3.dvSideMin_mul`)
  pins `dvSideMin(q)=0` inside the pure `x`; the point hypothesis (`dvSideDeg=0`) plus the
  landed exact spacing law `dvSideLen_eq` (C.08) pins `dvSideMax(q)=dvSideMin(q)=0`; the
  defect-vanishing lemma above then reads `deg q = D′·dvSideMax(q) = 0`. Provided both as
  the raw arithmetic fact (`q.natDegree = 0`) and as the ready-to-use contradiction
  (`0 < q.natDegree → dvSideDeg ≠ 0`), matching the doc's own "— contradiction" phrasing.
- **Gauss descent** is the single reusable primitive MH.13 needs for §6.2's "each `qᵢ` is a
  monic `K₀`-divisor of a monic `O`-polynomial and `O` (a DVR) is integrally closed, so
  `qᵢ ∈ O[x]`" step — stated as `q ∣ f.map (algebraMap O Kv)` (`f`, `q` monic) ⟹
  `∃ q', q'.Monic ∧ q'.map (algebraMap O Kv) = q`. `IsIntegrallyClosed O` resolves as an
  instance from `[IsDomain O] [IsDiscreteValuationRing O]` (same instance chain already
  exercised by `C130lb.lean`'s neighboring Gauss-lemma transport — DVR ⟹ PID ⟹ UFD ⟹
  integrally closed). ~10-line proof via `Polynomial.isIntegral_coeff_of_dvd` +
  `IsIntegrallyClosed.isIntegral_iff` + `Polynomial.lifts_and_degree_eq_and_monic`; no
  re-derivation of Gauss's lemma, per the doc's own "classical, not new" framing.

## Explicitly out of scope (left for MH.13)

The `∏ᵢ qᵢ` factorization of a squarefree divisor into `K₀[x]`-irreducibles (needs the PID
factorization-existence API, e.g. `UniqueFactorizationMonoid`) and the per-prime placement
argument (§6.2's "Now: `qᵢ ∣ W` ⟹ … ✗; `qᵢ ∣ Q` ⟹ … ✗; so `qᵢ ∣ P`") are **not** built
here — per the node table, MH.12's named inputs are only MH.2 + mathlib, sized 60–110
lines, and MH.13 is the node that assembles MH.2 + MH.3 + MH.12 + the `Squarefree` API
into Theorem C. This file supplies exactly the three primitives MH.13 needs and nothing
of MH.13's own assembly.

## No carried hypotheses, no statement changes

Every declaration above is unconditionally proved against the landed MH.2 API and mathlib;
no `sorry`, no new axiom, no weakened statement relative to §6.1/§6.2's math content (the
defect-vanishing lemma is if anything stronger — symmetric — than the doc's prose reading).
No existing file was edited; only `C133mh12.lean` was added.
