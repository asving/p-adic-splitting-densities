# UNIT D4A — verdict: the μ₅ refinement stack's base, rows D4-00..D4-04 [2026-08-28]

**File:** `leanfinal/Uniformity/ChapC/C136e0.lean` (new; 1987 lines; namespace
`Uniformity.Density.Tower.C136e0`).
**Validator:** `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136e0.lean` —
exit 0, zero errors, zero warnings, **zero `sorry`**.
**Axiom footprint:** 97 `#print axioms` in the AxCheck footer; every report is Lean-core
only (`propext, Classical.choice, Quot.sound`) or axiom-free (`s2Mu5_slot_residue_zero`).
No new axiom, no `unsafe`.

Source: `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.3 rows D4-00..04, under
the [G5F 2026-08-28] admissibility record — `(1,1,171)` consumed strictly as OPERATOR
data over the landed depth-four tower; no `DeepTower.hproper` forged or implied.

## Per-row status

| row | status | landed anchors |
|---|---|---|
| **D4-00** support shell | **CLOSED** | `dv4Hgt`/`dv4Pin`/`dv4Supp` (inner read = `C136d0.dv3Supp` — the tower recursion, one level up), full zero/ne-top/add/negation bank + full endpoint/minimizer/convolution bank (`Dv4OnSide`, `dv4SideSet/Min`, `le/lt_line_dev4_term`, `dv4Supp_add_le_dv4Supp_mul`, `dv4Supp_mul_eq_add_of_endpoint_le`, `dv4SideSet_nonempty_of_ne_zero`). Parameter-free; mirrors C136d0 Parts 1+3 lemma-for-lemma with the `(Ψ₃,u₃,ℓ₃)` hypothesis block threaded. |
| **D4-01** μ₅ value/product | **CLOSED** | `s2Hgt₅` (= `toZ ∘ dv4Supp L Φ₂ 21 2 g₈ 85 2 g16 · 171 1`), zero/finiteness/add laws, ★ tooth `s2Hgt₅_g16 : s2Hgt₅ g16 = 171 = u₅` (+ chain form `s2Hgt₅_keyChain_four` and anti-drift pin `s2g16_eq_keyChain_four` to `C136d3.s2DepthFourKeyChain`); product clause landed as `s2Hgt₅_mul_unconditional`/`s2Hgt₅_mul_all` (survival folded into D4-02, per the row text). |
| **D4-02** μ₄ survival (genuine new core) | **CLOSED, UNCONDITIONAL** | generic `Mu4Equiv/Mu4Dvd/Mu4Minimal/Mu4Prime/IsMu4Key` at the level-4 valuation, `%ₘ`/`/ₘ` survival core (`dv3Supp_mul_modByKey_le/eq`, `dv3Supp_add_le_key_quot_add`), generic discharge `dv4ResSurv_of_mu4Key`; ★★ S2 discharge `s2_dv4ResSurv_at_171 : Dv4ResSurv L Φ₂ 21 2 g₈ 85 2 g16 171 1` from `C136d3.s2Mu4KeyPoly_g16` (toZ-bridged: `s2_isMu4Key_g16`), the landed grade `C136d2.g16_exactGrade` → `s2_dv3Supp_g16 = 170`, and the [G5F] tight floor `1·170 = 170 < 171`. |
| **D4-03** valuation/grades | **CLOSED** | `s2Hgt₅_one_eq_zero`, ★ UNCONDITIONAL `s2AddVal₅ := AddValuation.of ... (s2Hgt₅_mul_all)` (the D3-05 pattern: directly from the product law, no nonemptiness-gap machinery) + full `S2Mu5ExactGrade`/`S2Mu5AboveGrade` bank (iff-dv4Supp normal forms, exists/unique/mul/not_above/not_zero/above_zero/eq_addVal, `tooth_g16 : S2Mu5ExactGrade 171 g16`). |
| **D4-04** grade-line coordinates (refinement gate) | **CLOSED** | ★ `s2Mu5_def312_level5`: at `(e₅,h₅)=(1,171)` the unique Def-3.12 solution is `s₅(β)=0`, `u₅(β)=β` — **the unique slot residue is 0**; `s2Mu5_slot_residue_zero`; gate `S2Mu5SlotOnGrade` (+ `_iff`, collapsed residue law `s2Mu5SlotOnGrade_residue`, division-free inner pin `s2Mu5SlotOnGrade_inner_exact : S2Mu4ExactGrade (β−171·s)`, support bound `dv4Supp_le_of_mu5SlotOnGrade`); ★ `S2Mu5PrevGrade := 1 ∣ β` with `S2Mu5PrevGrade_all` — **PrevGrade is ALL grades**; level-4 ε-data Bézout pin `s2Mu5_bezout_level4 : 1·85 + (−42)·2 = 1` for D4-05. |

## Recorded deviations (honest scope)

1. **One file for five rows** — §5 names declarations, not files; the five rows are one
   dependency chain (exactly the D3 precedent: C136d0 landed D3-00/01/02,
   C136d3ad landed D3-03/04 together).
2. **D4-02 model swap** — discharged by the D3AD survival-mirror pattern
   (`C136d3ad.dv3ResSurv_of_mu3Key`, the closer landed template the campaign brief itself
   names), not a literal port of `C132nv3b.s2_dvSupp_mul_modByComposedKey_eq`.  The row's
   demanded μ₄-normalized-product mechanism enters through the landed key theorem
   `C136d3.s2Mu4KeyPoly_g16` (proved via `C136d2.s2Mu4NormRes_mul`'s criterion) and
   through the `hmul` supplier (`s2Hgt₄_mul_all` read backwards across `toZ`), whose own
   proof is D3-04's endpoint assembly at the discharged μ₃ survival.
3. **Tooth proof shape** — `s2Hgt₅_g16` pins the 17-slot inf by antisymmetry (slot-1 term
   = 171 exactly; slot 0 = ⊤; slots ≥ 1 have `171·j ≥ 171`) instead of C136d0's full
   `inf_insert` expansion; no `maxHeartbeats` bump was needed anywhere.

## What this unit does NOT claim

No μ₅ coefficient/graded/normalized operator (D4-05..09), no normalizer exact grade
(D4-10), no recipe/leaf (D4-11/12), no μ₅ key predicates over the μ₅ valuation
(D4-13..16), no source/calculus record (D4-17/18).  OPEN-RP1-TRANSPORT inherited as a
citation, never re-opened.  New statement shapes (all `def`s and predicate-introducing
theorems) are trust-boundary declarations flagged for human review in the file header.

## Downstream supply map

* D4-05 (recursive coefficient): gate `S2Mu5SlotOnGrade` + inner pin + `s2Mu5_bezout_level4`.
* D4-06..09 (graded/normalized operators): `s2Hgt₅` bank + `dv4Pin_top_of_gt` +
  `dv4Supp_le_term` + `S2Mu5ExactGrade` bank + `S2Mu5PrevGrade`.
* D4-10 (normalizer exact grade): `s2Hgt₅_mul_all`/`S2Mu5ExactGrade_mul` + `tooth_g16`;
  `C136d3.s2Mu5_chainNormBelow_four_one_seventy_one_chain` supplies the Λ polynomial.
* D4-13..15 / A8D direct-key twins: the generic `IsMu4Key` bank + `dv4SideSet` machinery
  are the exact shapes the μ₅ key rows repeat one level up.

Build: `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136e0.lean` → exit 0
(2026-08-28).  All four write-increments were verified green in sequence (Part 1 bank →
endpoint/convolution bank → generic key core → S2 instantiation), each compiling
first-pass.
