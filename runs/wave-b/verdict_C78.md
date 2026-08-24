# VERDICT — unit C78 (hard node C.78, `partial_block_decision`, the FGMN block-decision existential)

**Date:** 2026-08-24 · **Status: LANDED (adjudication + machine-checked instance core) / SUPPLY (universal proof — missing objects named below)**

## Adjudication: **TRUE**

The signed C.78 is NOT a sixth D-CARRY refutation. It is the faithful FGMN order-2
theorem-of-the-residual-polynomial dictionary (partial-side entry), in the corpus's cleared
normalization: `dv2Hgt = (e₁e₂)·v` (= C131t's `WT` weight), so the signed `(u₃, ℓ₃)` in lowest
terms IS FGMN's `(h₂, e₃)`, and the composite degree `(e₁e₂ℓ₃)(f₁f₂·deg r₂)` is the published
formula verbatim. The five refuted siblings asserted an exact degree OF the choice-block from
floor data; C.78 asserts a DIVISOR at the composite degree — the shape the dictionary supplies.
Co-factor soundness (side read on `f`, conclusion on `blockFactor`): above the seam floor
`hfloor₃`, the non-block part contributes only a constant polygon translation (Minkowski
additivity — the same FGMN Thm 2.8 content already print-read for `fgmn_dv_exact_mul`), so
slopes, lengths, residual-factor multiplicities, and separability all transfer.

**Decisive machine evidence (all in `leanfinal/Uniformity/ChapC/C78adj.lean`, Lean-core):**
at the tower-borne probe `(s2Tower, f₅)` over any `(O, 2, q=2)` — the SAME instance whose
floor slack (`deg f₅ = 5`, `D₂ = 4`) machine-refuted C.77(iii) and C.80 (`5 = 4`) — every
hypothesis of C.78 is inhabited at `(u₃, ℓ₃, r₂) = (13, 1, X+1)` and the exact-degree
existential FIRES: a monic degree-4 divisor of `blockFactor = f₅` exists (Hensel). The defeat
mechanism structurally cannot reach C.78's shape.

**Numeric certificate** (`runs/wave-b/cert_C78_probe.py`, exact 2-adic to 2⁶⁰): root
`z ≡ 3 (mod 8)`; cofactor `g₄` monic, coefficient valuations `(2,2,7,2)`; the quadratic-split
search `g₄ = q₁q₂` **dies already mod 2³** (so `g₄` is irreducible over ℚ₂, `(e,f) = (4,1)` —
`v(Φ′(θ)) = 5/4` forces `4 ∣ e`); pins `(13, 0)` for every choice of the noncanonical
`resLift` unit `w` (incl. `w = −1`); `v₂(Res(f₅, Φ₂)) = 13` — the polygon's prediction exact.
So the FULL signed conclusion (incl. the conditional `typeOf` clause, whose box hypotheses are
free at the probe since `f₁f₂·deg r₂ = 1`) is true at the instance.

## Landed declarations (namespace `Uniformity.Density.Tower.C78adj`; footprints ALL `{propext, Classical.choice, Quot.sound}` — 19 `#print axioms`, zero `sorry`, zero warnings, NO cite inherited)

* `composedKey_s2Tower` — first explicit composed key: `Φ₂ = Φ′² − C(w·4)·X`, `w = resLift`-unit
  (`slotIdx_five`, `wrapExp_s2_zero`, `stageCoord_one`, `entryW`, `residue_entryW`, `isUnit_entryW`).
* `dev₂_f₅_zero/one/ge_two` — the `Φ₂`-digits `(4wx² + (4w+4)x + 8, x+1, 0…)`.
* `dvhgt_D0_one` (= 4 exact), `dvhgt_D0_zero_ge` (≥ 7 — the q=2 collapse `v(4w+4) ≥ 3`),
  `dvsupp_D0` (= 13, the seam-cancellation pin, choice-independent), `dvsupp_X1` (= 0),
  full level-1 side data of both digits.
* `dv2Res_pinned` — the `Exists.choose` resolution for C.38a's `dv2Res` (the "lemma nobody has
  stated" from C.38a's own docstring; reusable instrument).
* `dv2Pin_f₅_zero/one/ge_two`, `dv2supp_f₅`, `hne₃_f₅`, `dv2sidemin/max/deg_f₅` — the first
  dv2-level side in the corpus: `{0,1}` at `(13,1)`, `dv2SideDeg = 1`, floor `10 < 13` strict.
* `dv2respoly_f₅` (= `X + 1`), `dv2respoly_f₅_separable`, `r₂_monic/natDegree/irreducible/dvd`
  — C.78's full hypothesis package inhabited.
* `exists_root_f₅` (Hensel via `IsAdicComplete → HenselianRing`; `f₅(3) = 216 ∈ 𝔪`,
  `f₅′(3) = 389` unit), `exists_monic_deg_four_divisor`,
  ★ `partialBlockDecision_core_at_probe` — the conclusion core at the exact composite degree.
* `PartialBlockDecisionStatement` — the ∀-closure Prop carrier of the signed type (C.61
  precedent). NOT proved, NOT refuted, NOT an axiom.

## No re-sign proposed

The statement stays byte-frozen at its leanspec stub. HX_SWEEP §7's registry row should be
updated by the orchestrator to: **ADJUDICATED TRUE (C78adj.lean; instance core machine-checked;
universal = order-2 dictionary, awaiting carrier/cite)** — 8 of 8 sites now dispositioned.

## SUPPLY — what the universal proof needs (named objects)

1. **An order-2 factorization carrier or cite**: either C.78 becomes a consumer of the
   `FGMNCalculus`/`ChainRealization` path (CC-16, in flight — the natural home: the dictionary
   clause is field-shaped), or a gate-(b) cite of FGMN's order-2 theorem of the residual
   polynomial (same J. Algebra 427 (2015) paper as `fgmn_dv_exact_mul`; print-read + owner
   review-list row required — NOT declared by this unit).
2. **The probe's conditional-clause instance** (optional strengthening, both legs certified
   numerically): `Irreducible g₄` by the mod-8 coefficient contradiction (BFS obstruction at
   2³), and `inertiaDegOf g₄ = 1` via coprime norm values `{4, 5}` (`natDegree_mem_normValues`
   + `v(N(θ²−2)) = 5`, computable by companion-matrix `Matrix.det_fin_four`); then C.61's
   sandwich (`factorizationType_eq_of_dvd`) closes `typeOf g₄ = ⟨{(4,1)}⟩`.

## Verification

```
cd leanfinal && lake env lean Uniformity/ChapC/C78adj.lean   # 0 errors, 0 warnings, 19 Lean-core axiom prints
python3 runs/wave-b/cert_C78_probe.py                        # from repo root: the numeric certificate
```
