# Verdict — unit RP0: S2-source plan node RP-0 (grade arithmetic)

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row RP-0
"grade arithmetic" (deps `NV-5`, S2 numerals `(2,1,5)`). File created (the ONLY file
touched): `leanfinal/Uniformity/ChapC/C130rp0.lean` (19 public declarations; not added to
`Uniformity/ChapC.lean` or any roll-up).

## RP-0 (grade arithmetic) — LANDED

Fixed the CONCRETE S2 instantiation of `FGMNSourceData.ExactGrade`/`AboveGrade`
(`C130fg.lean`'s abstract shape `S.nextValue g = (β : WithTop ℤ)` /
`(β : WithTop ℤ) < S.nextValue g`) with `nextValue := s2Hgt₂ h2 hq` (the landed level-two
cleared value, U9 §2's `μ₂` at `(e',f',u') = (2,1,5)`): `S2ExactGrade`/`S2AboveGrade`, free-
standing `Prop`s, no `FGMNSourceData` instance built. Landed the bank: the value-group
helper `toZ_lt_toZ_iff` (the strict companion of C130s6's `toZ_le_toZ_iff`) and
`S2Grade_natCast_add`; the exact-/above-membership normal forms `S2ExactGrade_iff_dvSupp` /
`S2AboveGrade_iff_dvSupp` (derived via `toZ_inj`/cast compatibility down to the `ℕ∞`-valued
`dvSupp` read — the honest cleared normalization, not guessed); grade existence
(`S2ExactGrade_exists`, every nonzero polynomial has a genuinely NATURAL grade) and
uniqueness (`S2ExactGrade_unique`); ★ the grade arithmetic `S2ExactGrade_mul` (exact + exact
→ exact under multiplication, unconditional, direct from C130nv3's now-universal
`s2Hgt₂_mul` — the grade half of published Cor 4.12(2) that RP-3/RP-6 consume, no
`PrevGrade` premise per U9 Q3) and its dual `S2ExactGrade_not_above`; the zero/⊤ edge cases
(`S2ExactGrade_not_zero`/`S2ExactGrade_zero_false`, `S2AboveGrade_zero`); the NV-5 tie
(`S2ExactGrade_eq_addVal`/`S2AboveGrade_eq_addVal`, both predicates read off C130nv5's
packaged `s2AddVal₂` verbatim, so the bank is not an ad hoc reinvention). Numeral teeth:
`h₂(x)=2`, `h₂(Φ′)=5` (landed, restated as exact grades) and the two NEW composites
`h₂(x·Φ′)=7=2+5`, `h₂(Φ′²)=10=5+5`, both produced by `S2ExactGrade_mul` alone with zero
fresh computation.

## One real trap (recorded, fixed, not a divergence)

Docstring text containing the literal substring "exact-/above-membership" terminates a
Lean block comment early (`-/` is the comment closer regardless of surrounding prose),
producing a cascade of unrelated parse errors starting mid-docstring. Fixed by rewording to
"exact- and above-membership" in both occurrences; no content lost.

## What was deliberately NOT claimed

No `gradedResidual`/`Rgr`/`normalizedResidual`/`Rres` (RP-1 onward); no
`FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance (FD-0); `S2ExactGrade_mul`
proves only the grade-exactness conjunct of Cor 4.12(2), not the residual-value conjunct
(RP-3–RP-6's CORE chain).

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp0.lean` — CLEAN (0 errors, 0
warnings, 0 sorry). `lake build Uniformity.ChapC.C130rp0` — success (8740 jobs). 19
`#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]` (Lean-core only); no
new axiom, no `unsafe`. No git commit (per brief).
