# Verdict — unit NP0: S2-source plan node NP-0 (points and evaluation)

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row NP-0.
File created (the ONLY repo file touched): `leanfinal/Uniformity/ChapC/C130np0.lean`
(59 public declarations; not added to `Uniformity/ChapC.lean` or any roll-up).

## VERDICT: COMPLETE, with one genuine design discovery

**The stage-1 `valueOn` is NEITHER landed extension.** The interface's `slot_value`
(tie to NP-1's level-one table `s2Hgt₁` on `natDegree < Dcum 1 = 2`) and `key_value`
(gauge-live `i = 1`: `pointHgt 1 x (keyAt 1) = u₂ = 5`) JOINTLY pin the stage-1 point
valuation, and both landed candidates fail one leg: `s2AddEVal₁` (the `s2Hgt₁`
extension) reads `s2Hgt₁ (x² − 2) = 2 ≠ 5` on the key; `s2AddEVal₂` (the `s2Hgt₂`
extension) reads `4 ≠ 2 = s2Hgt₁ (C 2)` on the slot. The valuation satisfying BOTH is
the MacLane augmentation `[μ₁; Φ′ : 5]` — in the landed carrier,
`s2PHgt₁ := toZ (dvSupp (s2Frame h2 hq) · 5 1)` (the `(u, ℓ) = (5, 1)`-cleared
development support). Constructed here end-to-end:

1. **Bank**: zero / ne_top / eq_top_iff / add_ge, the small-degree dictionary
   `s2PHgt₁ = s2Hgt₁` on `natDegree < 2` (★ the `slot_value` tie), the key read
   `s2PHgt₁ (Φ′) = 5` (★ the `key_value` read), all from the GENERIC `(u, ℓ)` dvSupp
   layer (C130s6) — no new induction.
2. **Product law at `(5, 1)`** (`s2P_dvSupp_mul`, `s2PHgt₁_mul`, universal, no fences):
   assembled from the SAME generic NV-2 endpoint bank and the SAME parameter-free NV-3
   S2 survival core (`s2_stageHeight_mul_modByMonic_le`); only the admissibility
   numerals change (`1·2 < 5` for `2·2 < 5`). No NV-2/NV-3-scale work was redone.
3. **Packaging + extension** (mirror of C130nv5): `s2PAddVal₁` → `s2PVal₁` →
   `s2EPVal₁ = extendToLocalization` → `s2AddEPVal₁ : AddValuation E (WithTop ℤ)` on
   `E = FractionRing (Polynomial O)`, with the restriction PIN `s2AddEPVal₁_algebraMap`
   (NV56's 0/⊤ instance-chain trap avoided by the same supp-ideal route).

## The NP-0 deliverables (each probe-checked at the LITERAL instantiated field type)

* `S2NPPoint := Unit` (plan §5.1's sanctioned carrier), `s2NPPt i x` = the VALUE
  EQUATIONS (no unproved `True`): gauge-live exact key value `u_{i+1}` ∧ key finiteness.
* `s2NPCoeffHom := s2EvalHom`, `s2NPCoord _ := s2EvalCoord` — SF-4's probe pair verbatim
  (injective coefficient read, rational-function coordinate).
* ★ Bridge `s2NP_eval₂_eq_algebraMap`: at this pair `eval₂ coeffHom (coord x)` IS
  `algebraMap (Polynomial O) E` — every point read becomes a landed polynomial value.
* `s2NPValueOn i` = `s2AddEPVal₁` (i ≤ 1) / NV-6's `s2AddEVal₂` (i ≥ 2); all four value
  laws hold UNFENCED (∀ i, from the `AddValuation` structure incl. mathlib's
  `map_add_of_distinct_val`), field-shaped versions supplied.
* `s2NPPointHgt i x A := valueOn i (eval₂ …)` — so `pointHgt_eval` is `rfl`; restriction
  dictionaries `s2NPPointHgt_one = s2PHgt₁`, `s2NPPointHgt_two = s2Hgt₂` for ALL `A`.
* **Field shapes proved**: `point_exists` (both live stages), `pointHgt_eval`,
  `value_zero/mul/add_ge/add_eq`, **`slot_value` at BOTH live levels** (against
  `s2NPHgt := s2Hgt₁/s2Hgt₂`; the `hgt_two` frontier tie is `rfl`) and **`key_value` at
  gauge level 1** — i.e. plan row NP-2's two halves are already dischargeable here —
  plus the finiteness half of `window`, and the `grade_compat` shape for
  `fgmn.nextValue := s2Hgt₂` (probe-checked; feeds FD-1).
* Teeth: the EXACT U13 refutation slot, now live and stage-graded —
  `pointHgt 2 x (C 2) = 4` (new named value `s2Hgt₂_C_two`), `pointHgt 1 x (C 2) = 2`,
  `pointHgt 1 x (Φ′) = 5 ≠ 2` (the computation that kills `s2AddEVal₁` as `valueOn 1`).

## BLOCKED / deferred fields (named per plan rows; none silently dropped)

`pointDig`/`slot_digit`/`dig_add`-at-point → **NP-3** (needs RP-2's residual reads; free
digit copy disallowed). `thresholdZ/Nat`, `threshold_nonneg`, window's threshold half →
**NP-4/NP-5** (no named source occurrence; numeral would be circular). Letters/reads →
**NP-6/7/8**. Stage-law `i`-fencing of the landed per-level banks → SG-0 assembly. No
`SplitNodePointSource` instance claimed (SG-0).

## Verification

`lake env lean Uniformity/ChapC/C130np0.lean` — CLEAN (exit 0, 0 errors, 0 warnings,
0 sorry); 59 `#print axioms` rows: 57 exactly `[propext, Classical.choice, Quot.sound]`,
2 axiom-free pure defs (`S2NPPoint`, `s2NPPointMk`); no sorryAx anywhere.
`lake build Uniformity.ChapC.C130np0` — success (8754 jobs; olean available to NP-2/NP-5/
SG-0). Acceptance probe (`/tmp/np0_probe.lean`, not in the repo): every deliverable
elaborates at the literal instantiated `SplitNodePointSource` field type (incl.
`slot_value` at `W.Dcum`, `key_value` at `W.u`/`K.keyAt`). `git status`: only
`C130np0.lean` added; no other unit's file touched; no commit (per brief).
