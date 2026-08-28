# VERDICT — UNIT A0G2 (node A0G-CV, degree-generic coefficient boxes)

**Date:** 2026-08-28 · **File:** `leanfinal/Uniformity/ChapI/IFCG1.lean` (NEW, 527 lines)
**Status: PROVED — file green, zero `sorry`, all 28 AxCheck footprints Lean-core only
(`propext, Classical.choice, Quot.sound`).**
Verified per discipline: `timeout 580 lake env lean Uniformity/ChapI/IFCG1.lean` — clean
(no errors, no warnings), 28/28 `#print axioms` lines are Lean-core.

## What landed

The A0G-CV row of `docs/in-progress/A0_GENERAL_2026-08-28.md` §6, in namespace
`Uniformity.Density.IFCG1`:

1. **`shiftVecN`** — the degree-generic recentring vector (coefficients of `F_a(X+γ)`), plus
   `monicPoly_shiftVecN`, `typeOf_shiftVecN` (**direct consumption of the landed
   `typeOf_shift`**, HYP.05), group law `shiftVecN_zero`/`shiftVecN_add`, involution
   `shiftVecN_shiftVecN_neg`, the arbitrary-modulus congruence transport `dvd_shiftVecN_sub`
   (+ `dvd_pow_shiftVecN_sub` in the models' `π^N` phrasing, `proj_shiftVecN_congr` at class
   level), and the explicit binomial coefficient law `shiftVecN_apply`
   (`C(n,i)γ^(n−i) + Σ_j C(j,i)a_j γ^(j−i)`, via Taylor/Hasse derivative) with the evaluation
   pins `shiftVecN_coeff_zero` (= `F(γ)`) and `shiftVecN_coeff_one` (= `F′(γ)`).
2. **Translation bijections** — `shiftEquivN : (Fin n → O) ≃ (Fin n → O)` (vector level) and
   `coeffShiftEquivN : Coeff O n N ≃ Coeff O n N` (level-`N` class level), with the lift law
   `coeffShiftEquivN_proj`, the counting invariance `card_image_coeffShiftEquivN`, and the
   generic certificate transport `decidedAt_of_shiftVecN_cert` (arbitrary depth `k ≤ M`; the
   degree-generic `H97r3.decidedAt_of_shift_cert`).
3. **`MBoxN O n M := (i : Fin n) → Res O (M + i)`** — the degree-generic mixed-precision box
   (dependent-Pi generalization of H97r3's triple product), with `mtruncN` (AddMonoidHom),
   `mtruncN_surjective`, `mkBoxN` + `mtruncN_mkBoxN` + `mkBoxN_surjective`, the record iff
   `mkBoxN_eq_iff_dvd`, and the no-loss multiplication-back-up lemma
   `dvd_extract_sub_of_mkBoxN_eq` (extraction `b i = π^(n−i)·d i` + equal records ⇒ full
   `π^(M+n)` congruence — the degree-generic mechanism of H97r3's sharp count).
4. **EXACT box cardinalities** — `card_MBoxN : #(MBoxN O n M) = q^(nM + n(n−1)/2)` (the
   excess is §3.2's `κ_n = n(n−1)/2`), the proportion law `card_preimage_mtruncN`, and the
   exact fibre law `card_preimage_mtruncN_eq : #(mtruncN⁻¹S) = #S · q^(n(n−1)/2)`.

## GATE (all satisfied)

* **n = 2, 3 recovery:** `shiftVecN_three` (= landed `H97r1.shiftVec`), `shiftVecN_two`
  (= landed `IFC7.shiftVec2`) — both proved by `monicPoly`-injectivity against the landed
  `monicPoly_shiftVec`/`monicPoly_shiftVec2`; `mboxEquivThree : MBoxN O 3 M ≃ MBox O M` with
  `mboxEquivThree_mkBoxN` **literally `rfl`** (the definitional instantiation: the generic
  record at n=3 IS H97r3's `mkBox`), `mtrunc_mboxEquivThree` (recovers `mtrunc`),
  `card_MBoxN_eq_card_mbox`, and the exponent pins `card_MBoxN_three` (`3M+3`, the landed
  `card_mbox` exponent) and `card_MBoxN_two` (`2M+1`, `κ_2 = 1`). The landed cubic
  certificate wrapper is re-derived from the generic transport
  (`decidedAt_of_shift_cert_recover`, n=3/k=3/level M+3).
* **No `Fin 3` (or any fixed-degree type) in public signatures** of the generic API
  (§§0–4); fixed degrees occur ONLY in §5, which is exactly the mandated recovery bank
  (checked by grep: first code occurrence of `Fin 3`/`Fin 2` is line 428, §5 starts 418).
* **`typeOf_shift` consumed** directly in `typeOf_shiftVecN`.

## Dedup finding (important for the campaign map)

A degree-generic recentring ALREADY LANDED at **H.123a**
(`Uniformity.Density.Induction.recentreVec` + `monicPoly_recentreVec` +
`recentreVec_recentreVec` + `proj_recentreVec_congr` + the class-level `recentreClass` bank
incl. `decidedAt_recentreClass`/`undecidedAt_recentreClass_iff`), which the A0G-CV row's
"exact landed inputs" list did not mention. Per dedup discipline, `shiftVecN` is a
**reducible wrapper** over `Induction.recentreVec` (`shiftVecN_def` is `rfl`), and every
H123a lemma is consumed as-is; nothing was re-derived. **The A0 doc's §3.3 claim that "none
of the `Fin 3` carrier is reusable as-is" should be amended:** the recentring carrier was
already generic; only the mixed box, the cardinalities, the group law/bijection packaging,
the explicit coefficient law, and the generic certificate transport were missing — they are
what this file adds.

## Size note

527 lines vs the row's 700–1200 estimate: the shortfall is exactly the H123a dedup (the row
budgeted a from-scratch recentring). No planned deliverable was dropped.

## Downstream (per the §6 critical path)

* A0G-NP/GC consume `decidedAt_of_shiftVecN_cert`, `coeffShiftEquivN`, `shiftVecN_apply`.
* A0G-RS consumes `MBoxN`/`mkBoxN_eq_iff_dvd`/`dvd_extract_sub_of_mkBoxN_eq` +
  `card_preimage_mtruncN_eq` (the `κ_m` loss is the `q^(n(n−1)/2)` fibre factor here).
* Suggested follow-up (not in this node's scope): the subleading pin
  `shiftVecN a γ (n−1) = a(n−1) + n·γ` as a corollary of `shiftVecN_apply`, if A0G-RS wants
  it pre-packaged.

## Trust boundary

All 28 exported theorems are NEW statements (flagged for the standing review); no landed
file touched; no new axiom; footprint Lean-core throughout.
