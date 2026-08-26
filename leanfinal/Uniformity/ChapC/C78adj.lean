/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C80
import Uniformity.ChapC.C128
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C47
import Uniformity.ChapC.C53b
import Uniformity.ChapC.C60
import Mathlib.RingTheory.Henselian

/-!
# Uniformity.ChapC.C78adj — C.78 (`partial_block_decision`) ADJUDICATED TRUE at the probe

**Chapter C, NODE C.78** — the FGMN block-decision existential, the LONE unadjudicated member
of the EXACT-DEGREE (D-CARRY) family after A-C.10 (HX_SWEEP §7: "CANDIDATE, DIFFERENT SHAPE").
This file adjudicates it: **TRUE** — the signed statement is NOT a sixth refutation; it is the
faithful FGMN order-2 dictionary (partial-side entry), and the very probe `(s2Tower, f₅)` that
machine-refuted C.77(iii) and C.80 SATISFIES C.78 instead.

## What lands here (all Lean-core; no cite, no `sorry`)

1. **The first dv2-level instantiation in the corpus.** Every hypothesis of the signed C.78 is
   INHABITED at `(s2Tower, f₅, u₃ = 13, ℓ₃ = 1, r₂ = X + 1)` over any `(O, 2, q = 2)`:
   the composed key computes to `Φ₂ = Φ′² − C(4w)·X` with `w` a UNIT (`composedKey_s2Tower`);
   the `Φ₂`-digits of `f₅` are `(4wx² + (4w+4)x + 8, x + 1)`; the dv2-pins are `(13, 0, ⊤, …)`
   — the two weight-10 seam terms CANCEL (the digit-0 pin is 13 exactly, for EVERY choice of
   the noncanonical `resLift` unit `w`, because `w ≡ 1 (mod 𝔪)` forces `v(4w + 4) ≥ 3`: the
   q = 2 collapse again); the dv2-side at `(13, 1)` is `{0, 1}` with `dv2SideDeg = 1`; and the
   level-2 residual is `dv2ResPoly = X + 1` — separable, monic, irreducible over the field
   `AdjoinRoot (towerLabel s2Tower)`, its own divisor. Note `hfloor₃ : 1·E₂ = 10 < 13`: the
   side sits strictly ABOVE the seam, exactly the regime the signed statement quantifies over.
2. **The exact-degree existential FIRES** (`partialBlockDecision_core_at_probe`): a monic
   divisor `g` of `blockFactor (levelDatum) f₅ = f₅` with
   `deg g = (e₁·e₂·ℓ₃)·(f₁·f₂·deg r₂) = (2·2·1)·(1·1·1) = 4` EXISTS — via Hensel
   (`IsAdicComplete → HenselianRing`): `f₅(3) = 216 ∈ 𝔪`, `f₅′(3) = 389` a unit, so `f₅` has a
   root `z` and `g := f₅ /ₘ (X − C z)` is monic of degree 4. **The D-CARRY defeat mechanism
   cannot fire on C.78's shape**: `deg f₅ = 5` with floor slack `s = 1` is precisely the
   instance where the five refuted siblings demanded `5 = 4` — here the conclusion demands a
   DIVISOR at the composite degree 4, and `f₅ = (X − z)·g₄` supplies it.
3. **The ∀-closure Prop carrier** (`PartialBlockDecisionStatement`) — the exact signed type,
   for future units to name without re-transcribing (C.61's `Tier1TypeOfStatement` precedent).
   It is NOT proved and NOT refuted here; the signed axiom stays at its leanspec stub.

## The adjudication record (why TRUE, and what the full proof still needs)

* The five A-C.10 refutations all had the shape "exact degree of the `Classical.choice` block
  asserted from floor-divided data" — refuted because `deg f = D₂·m̄ + s` slack is invisible.
  C.78's conclusion is an ∃: the FGMN theorem of the residual polynomial at order 2 (each
  side of slope `> T₂` of the `Φ₂`-polygon, each irreducible factor `r₂` of its separable
  residual, yields ONE monic factor of the block at degree `e₁e₂ℓ₃·f₁f₂·deg r₂`). The cleared
  normalization matches: `dv2Hgt = (e₁e₂)·v` (C131t's `WT` weight), so the signed `(u₃, ℓ₃)`
  in lowest terms IS FGMN's `(h₂, e₃)`, and the composite degree formula is verbatim.
* NUMERIC CERTIFICATE (session companion run, 2026-08-24, exact 2-adic arithmetic to 2⁶⁰):
  root `z ≡ 3 (mod 8)`; cofactor `g₄` monic, coefficient valuations `(2, 2, 7, 2)`; the
  quadratic-split search `g₄ = q₁q₂` DIES already mod 2³ (so `g₄` is irreducible over `ℚ₂`,
  with `(e, f) = (4, 1)` — `v(Φ′(θ)) = 5/4` forces `4 ∣ e`); `v₂(Res(f₅, Φ₂)) = 13` — the
  polygon's prediction on the nose. So the FULL signed conclusion (including the conditional
  `typeOf g = {(4,1)} ∧ Irreducible g` clause, whose box hypotheses are FREE at the probe
  since `f₁·f₂·deg r₂ = 1`) is TRUE at the probe; the Lean landing of that final clause needs
  `Irreducible g₄` (a mod-8 coefficient contradiction, certified above) plus
  `inertiaDegOf g₄ = 1` (two coprime norm values, e.g. `4 = deg` and `5 = v(N(θ² − 2))`) and
  is left as named open work, NOT claimed here.
* The UNIVERSAL statement is the order-2 dictionary itself. Its Lean discharge needs an
  order-2 factorization carrier (the `FGMNCalculus`/`ChainRealization` path, CC-16), or a
  faithful order-2 cite; neither is landed, and NO new axiom is declared here. C.78 therefore
  stays at its leanspec stub, adjudicated TRUE with the instance machine-checked.

## Status

Zero `sorry`; axiom footprint of every declaration: Lean core (AxCheck footer). No cite.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Tower.C78adj

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 0. Card-2 collapse helpers (C80's private lemmas, re-derived) -/

private theorem eq_one_of_card_two {K : Type*} [Field K] (hcard : Nat.card K = 2)
    {z : K} (hz : z ≠ 0) : z = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hz.isUnit.unit = 1 := Subsingleton.elim _ _
  calc z = ((hz.isUnit.unit : Kˣ) : K) := (hz.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

include hq in
private theorem res_one_add_one : (1 + 1 : ResidueField O) = 0 := by
  by_contra hne
  have h1 : (1 + 1 : ResidueField O) = 1 := eq_one_of_card_two hq hne
  exact one_ne_zero (α := ResidueField O) (by linear_combination h1)

include h2 in
private theorem two_mem_max : (2 : O) ∈ IsLocalRing.maximalIdeal O :=
  h2.not_isUnit

private theorem four_ne_zero (h2 : Irreducible (2 : O)) : (4 : O) ≠ 0 := by
  rw [show (4 : O) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 h2.ne_zero

/-! ## 1. The slot data of the composed key at the s2 frame -/

include h2 hq in
theorem slotIdx_five : (s2Frame h2 hq).slotIdx 5 = 1 := by
  refine ((s2Frame h2 hq).slotIdx_unique (k := 5) (i := 1) ?_ ?_).symm
  · rw [e1_eq h2 hq]; norm_num
  · rw [h_eq h2 hq, e1_eq h2 hq]; decide

include h2 hq in
theorem wrapExp_s2_zero : wrapExp (s2Tower h2 hq) 0 = 0 := by
  rw [wrapExp]
  show (1 - 0) * (s2Frame h2 hq).slotIdx 5 / (s2Frame h2 hq).e₁ = 0
  rw [slotIdx_five h2 hq, e1_eq h2 hq]

include h2 hq in
theorem stageCoord_one :
    (s2Frame h2 hq).stageCoord 1 (s2Frame_pin h2 hq) 1 0 = 1 := by
  have hdim : 0 < ((s2Frame h2 hq).stagePB 1 (s2Frame_pin h2 hq)).dim := by
    rw [KeyFrame.stagePB_dim, f1_eq h2 hq]
    norm_num
  rw [KeyFrame.stageCoord, dif_pos hdim]
  have hb : ((s2Frame h2 hq).stagePB 1 (s2Frame_pin h2 hq)).basis ⟨0, hdim⟩
      = (1 : (s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) := by
    simp [PowerBasis.coe_basis]
  rw [← hb, Module.Basis.repr_self, Finsupp.single_eq_same, map_one]

/-- **the entry coefficient `w`** — the noncanonical `resLift` unit carried by the composed
key's single lift monomial.  Everything provable about it: `residue w = 1` (a unit). -/
noncomputable def entryW : O :=
  resLift ((s2Frame h2 hq).stageCoord 1 (s2Frame_pin h2 hq) 1 0)

include h2 hq in
theorem residue_entryW : IsLocalRing.residue O (entryW h2 hq) = 1 := by
  rw [entryW, resLift_spec, stageCoord_one h2 hq]

include h2 hq in
theorem isUnit_entryW : IsUnit (entryW h2 hq) := by
  by_contra hu
  have hmem : entryW h2 hq ∈ IsLocalRing.maximalIdeal O := hu
  have h0 : IsLocalRing.residue O (entryW h2 hq) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [residue_entryW h2 hq] at h0
  exact one_ne_zero h0

include h2 hq in
theorem addVal_entryW : addVal O (entryW h2 hq) = 0 :=
  addVal_eq_zero_iff.mpr (isUnit_entryW h2 hq)

include h2 hq in
theorem entryW_mul_four_ne_zero : entryW h2 hq * 4 ≠ 0 :=
  mul_ne_zero (isUnit_entryW h2 hq).ne_zero (four_ne_zero h2)

include h2 hq in
/-- `v(w·4) = 2`. -/
theorem addVal_entryW_four : addVal O (entryW h2 hq * 4) = 2 := by
  rw [(addVal O).map_mul, addVal_entryW h2 hq, show (4 : O) = 2 ^ 2 by norm_num,
    addVal_two_pow h2, zero_add]
  rfl

include h2 hq in
/-- `1 ≤ v(w + 1)` — the q = 2 collapse: the unit `w` reduces to `1`, so `w + 1 ∈ 𝔪`. -/
theorem one_le_addVal_entryW_add_one : (1 : ℕ∞) ≤ addVal O (entryW h2 hq + 1) := by
  have hres : IsLocalRing.residue O (entryW h2 hq + 1) = 0 := by
    rw [map_add, residue_entryW h2 hq, map_one]
    exact res_one_add_one hq
  have hmem : entryW h2 hq + 1 ∈ IsLocalRing.maximalIdeal O :=
    Ideal.Quotient.eq_zero_iff_mem.mp hres
  have hdvd : (2 : O) ∣ entryW h2 hq + 1 := by
    have hspan := (irreducible_iff_uniformizer (2 : O)).mp h2
    rw [hspan] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  calc (1 : ℕ∞) = addVal O 2 := by
        rw [← pow_one (2 : O), addVal_two_pow h2, Nat.cast_one]
    _ ≤ addVal O (entryW h2 hq + 1) := addVal_le_iff_dvd.mpr hdvd

/-! ## 2. The composed key at the s2 tower: `Φ₂ = Φ′² − C(w·4)·X` -/

include h2 hq in
theorem composedKey_s2Tower :
    composedKey (s2Tower h2 hq)
      = s2Key O ^ 2 - Polynomial.C (entryW h2 hq * 4) * Polynomial.X := by
  rw [composedKey]
  rw [show (s2Tower h2 hq).f₂ = 1 from rfl, Finset.sum_range_one]
  rw [show (s2Tower h2 hq).e₂ * 1 = 2 from rfl, show (s2Tower h2 hq).e₂ * 0 = 0 from rfl,
    pow_zero, mul_one, show (1 - 0) * (s2Tower h2 hq).u₂ = 5 from rfl]
  have harg : -(s2Tower h2 hq).ψ₂.coeff 0
      * (s2Frame h2 hq).stageLetter 1 (s2Frame_pin h2 hq) ^ wrapExp (s2Tower h2 hq) 0
      = 1 := by
    rw [wrapExp_s2_zero h2 hq, pow_zero, mul_one]
    show -((Polynomial.X - Polynomial.C 1 :
      Polynomial ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))).coeff 0) = 1
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_neg]
  rw [harg, stageLiftO_of_f1 (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (f1_eq h2 hq) 5 1]
  rw [slotIdx_five h2 hq, h_eq h2 hq, e1_eq h2 hq, key_eq h2 hq,
    show (5 - 1 * 1) / 2 = 2 from rfl, pow_one, show ((2 : O) ^ 2) = 4 by norm_num]
  rfl

/-! ## 3. The `Φ₂`-digits of `f₅`: `(D0, X + 1, 0, 0, …)` -/

/-- **the digit-0 remainder** `D0 = 4w·x² + (4w + 4)·x + 8` — the two weight-10 seam terms of
`(x+1)·C(4w)x` and `f₅`'s tail have ALREADY interacted; the head coefficient `4w` carries the
pin 13. -/
noncomputable def D0 : Polynomial O :=
  Polynomial.C (entryW h2 hq * 4) * Polynomial.X ^ 2
    + Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X + Polynomial.C 8

include h2 hq in
private theorem f₅_eq_key₂ :
    f₅ O = (Polynomial.X + Polynomial.C 1) * composedKey (s2Tower h2 hq) + D0 h2 hq := by
  rw [f₅, composedKey_s2Tower h2 hq, D0, s2Key]
  simp only [map_add, map_mul, map_ofNat, map_one]
  ring

include h2 hq in
private theorem D0_degree_lt : (D0 h2 hq).degree < 4 := by
  rw [D0]
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by decide)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

include h2 hq in
theorem composedKey_s2Tower_natDegree : (composedKey (s2Tower h2 hq)).natDegree = 4 := by
  rw [composedKey_natDegree_D₂ (s2Tower h2 hq) h2, (s2Tower_data h2 hq).2.2.2.1]

include h2 hq in
private theorem composedKey_s2Tower_degree : (composedKey (s2Tower h2 hq)).degree = 4 := by
  rw [Polynomial.degree_eq_natDegree (composedKey_monic (s2Tower h2 hq)).ne_zero,
    composedKey_s2Tower_natDegree h2 hq]
  rfl

include h2 hq in
theorem dev₂_f₅_zero : dev (composedKey (s2Tower h2 hq)) (f₅ O) 0 = D0 h2 hq := by
  show (f₅ O) %ₘ composedKey (s2Tower h2 hq) = _
  refine (Polynomial.div_modByMonic_unique (Polynomial.X + Polynomial.C 1) _
    (composedKey_monic (s2Tower h2 hq)) ⟨?_, ?_⟩).2
  · rw [f₅_eq_key₂ h2 hq]; ring
  · rw [composedKey_s2Tower_degree h2 hq]
    exact D0_degree_lt h2 hq

include h2 hq in
private theorem f₅_div_key₂ :
    (f₅ O) /ₘ composedKey (s2Tower h2 hq) = Polynomial.X + Polynomial.C 1 := by
  refine (Polynomial.div_modByMonic_unique (Polynomial.X + Polynomial.C 1) (D0 h2 hq)
    (composedKey_monic (s2Tower h2 hq)) ⟨?_, ?_⟩).1
  · rw [f₅_eq_key₂ h2 hq]; ring
  · rw [composedKey_s2Tower_degree h2 hq]
    exact D0_degree_lt h2 hq

include h2 hq in
theorem dev₂_f₅_one :
    dev (composedKey (s2Tower h2 hq)) (f₅ O) 1 = Polynomial.X + Polynomial.C 1 := by
  show ((f₅ O) /ₘ composedKey (s2Tower h2 hq)) %ₘ composedKey (s2Tower h2 hq) = _
  rw [f₅_div_key₂ h2 hq]
  refine (Polynomial.modByMonic_eq_self_iff (composedKey_monic (s2Tower h2 hq))).mpr ?_
  rw [composedKey_s2Tower_degree h2 hq, Polynomial.degree_X_add_C]
  decide

include h2 hq in
theorem dev₂_f₅_ge_two (j : ℕ) (hj : 2 ≤ j) :
    dev (composedKey (s2Tower h2 hq)) (f₅ O) j = 0 := by
  refine dev_eq_zero_of_lt (composedKey_monic (s2Tower h2 hq))
    (by rw [composedKey_s2Tower_natDegree h2 hq]; norm_num) _ _ ?_
  rw [f₅_natDegree, composedKey_s2Tower_natDegree h2 hq]
  omega

/-! ## 4. The `Φ′`-digits of the two `Φ₂`-digits, and their level-1 heights -/

include h2 hq in
private theorem dev_D0_zero :
    dev (s2Key O) (D0 h2 hq) 0
      = Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X
          + Polynomial.C (entryW h2 hq * 8 + 8) := by
  show (D0 h2 hq) %ₘ (s2Key O) = _
  refine (Polynomial.div_modByMonic_unique (Polynomial.C (entryW h2 hq * 4)) _ s2Key_monic
    ⟨?_, ?_⟩).2
  · rw [D0, s2Key]
    simp only [map_add, map_mul, map_ofNat]
    ring
  · rw [s2Key_deg]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

include h2 hq in
private theorem D0_div : (D0 h2 hq) /ₘ (s2Key O) = Polynomial.C (entryW h2 hq * 4) := by
  refine (Polynomial.div_modByMonic_unique (Polynomial.C (entryW h2 hq * 4))
    (Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X + Polynomial.C (entryW h2 hq * 8 + 8))
    s2Key_monic ⟨?_, ?_⟩).1
  · rw [D0, s2Key]
    simp only [map_add, map_mul, map_ofNat]
    ring
  · rw [s2Key_deg]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

include h2 hq in
private theorem dev_D0_one :
    dev (s2Key O) (D0 h2 hq) 1 = Polynomial.C (entryW h2 hq * 4) := by
  show ((D0 h2 hq) /ₘ (s2Key O)) %ₘ (s2Key O) = _
  rw [D0_div h2 hq]
  refine (Polynomial.modByMonic_eq_self_iff s2Key_monic).mpr ?_
  rw [s2Key_deg]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

include h2 hq in
private theorem D0_natDegree : (D0 h2 hq).natDegree = 2 := by
  have h1 : (Polynomial.C (entryW h2 hq * 4) * Polynomial.X ^ 2).degree = ((2 : ℕ) : WithBot ℕ) :=
    Polynomial.degree_C_mul_X_pow 2 (entryW_mul_four_ne_zero h2 hq)
  have hBA : (Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X).degree
      < (Polynomial.C (entryW h2 hq * 4) * Polynomial.X ^ 2).degree := by
    rw [h1]
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  have hAB : (Polynomial.C (entryW h2 hq * 4) * Polynomial.X ^ 2
      + Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X).degree = ((2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt hBA, h1]
  have h8 : (Polynomial.C (8 : O)).degree
      < (Polynomial.C (entryW h2 hq * 4) * Polynomial.X ^ 2
          + Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X).degree := by
    rw [hAB]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  have hd : (D0 h2 hq).degree = ((2 : ℕ) : WithBot ℕ) := by
    rw [D0, Polynomial.degree_add_eq_left_of_degree_lt h8, hAB]
  exact Polynomial.natDegree_eq_of_degree_eq_some hd

include h2 hq in
private theorem dev_D0_ge_two (j : ℕ) (hj : 2 ≤ j) : dev (s2Key O) (D0 h2 hq) j = 0 := by
  refine dev_eq_zero_of_lt s2Key_monic (by rw [s2Key_natDegree]; norm_num) _ _ ?_
  rw [D0_natDegree h2 hq, s2Key_natDegree]
  omega

include h2 hq in
/-- the head digit's height is EXACTLY 4: `2·v(4w) = 4`. -/
theorem dvhgt_D0_one : dvHgt (s2Frame h2 hq) (D0 h2 hq) 1 = (4 : ℕ∞) := by
  rw [dvHgt, key_eq h2 hq, dev_D0_one h2 hq, KeyFrame.stageHeight_eq_inf]
  rw [Polynomial.natDegree_C, show Finset.range (0 + 1) = {0} from rfl]
  simp only [Finset.inf_singleton, Polynomial.coeff_C_zero, gaussVal_C, e1_eq h2 hq,
    h_eq h2 hq, addVal_entryW_four h2 hq]
  decide

include h2 hq in
/-- the tail digit's height is `≥ 7`: both coefficients are `4(w+1)`-shaped, `v ≥ 3`. -/
theorem dvhgt_D0_zero_ge : (7 : ℕ∞) ≤ dvHgt (s2Frame h2 hq) (D0 h2 hq) 0 := by
  rw [dvHgt, key_eq h2 hq, dev_D0_zero h2 hq, KeyFrame.stageHeight_eq_inf]
  refine Finset.le_inf ?_
  intro i hi
  have hde : (Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X
      + Polynomial.C (entryW h2 hq * 8 + 8)).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [Polynomial.natDegree_X])
    · rw [Polynomial.natDegree_C]; norm_num
  have hlt : i ≤ 1 := by
    have := Finset.mem_range.mp hi
    omega
  have hv1 : (3 : ℕ∞) ≤ addVal O (entryW h2 hq * 4 + 4) := by
    rw [show entryW h2 hq * 4 + 4 = 4 * (entryW h2 hq + 1) by ring, (addVal O).map_mul,
      show (4 : O) = 2 ^ 2 by norm_num, addVal_two_pow h2]
    calc (3 : ℕ∞) = ((2 : ℕ) : ℕ∞) + 1 := by decide
      _ ≤ ((2 : ℕ) : ℕ∞) + addVal O (entryW h2 hq + 1) :=
          add_le_add le_rfl (one_le_addVal_entryW_add_one h2 hq)
  have hv0 : (4 : ℕ∞) ≤ addVal O (entryW h2 hq * 8 + 8) := by
    rw [show entryW h2 hq * 8 + 8 = 8 * (entryW h2 hq + 1) by ring, (addVal O).map_mul,
      show (8 : O) = 2 ^ 3 by norm_num, addVal_two_pow h2]
    calc (4 : ℕ∞) = ((3 : ℕ) : ℕ∞) + 1 := by decide
      _ ≤ ((3 : ℕ) : ℕ∞) + addVal O (entryW h2 hq + 1) :=
          add_le_add le_rfl (one_le_addVal_entryW_add_one h2 hq)
  have hc0 : (Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X
      + Polynomial.C (entryW h2 hq * 8 + 8)).coeff 0 = entryW h2 hq * 8 + 8 := by
    simp
  have hc1 : (Polynomial.C (entryW h2 hq * 4 + 4) * Polynomial.X
      + Polynomial.C (entryW h2 hq * 8 + 8)).coeff 1 = entryW h2 hq * 4 + 4 := by
    simp
  interval_cases i
  · -- coefficient 0 = 8(w+1): `2 • v ≥ 8 ≥ 7`
    simp only [hc0, gaussVal_C, e1_eq h2 hq, h_eq h2 hq]
    refine le_trans (by decide : (7 : ℕ∞) ≤ 2 • (((4 : ℕ) : ℕ∞)) + (↑(1 : ℕ) * ↑(0 : ℕ))) ?_
    exact add_le_add (nsmul_le_nsmul_right hv0 2) le_rfl
  · -- coefficient 1 = 4(w+1): `2 • v + 1 ≥ 7`
    simp only [hc1, gaussVal_C, e1_eq h2 hq, h_eq h2 hq]
    refine le_trans (by decide : (7 : ℕ∞) ≤ 2 • (((3 : ℕ) : ℕ∞)) + (↑(1 : ℕ) * ↑(1 : ℕ))) ?_
    exact add_le_add (nsmul_le_nsmul_right hv1 2) le_rfl

include h2 hq in
theorem dvhgt_D0_ge_two (j : ℕ) (hj : 2 ≤ j) :
    dvHgt (s2Frame h2 hq) (D0 h2 hq) j = ⊤ := by
  rw [dvHgt, key_eq h2 hq, dev_D0_ge_two h2 hq j hj]
  exact sh_zero h2 hq

include h2 hq in
private theorem dev_X1_zero :
    dev (s2Key O) (Polynomial.X + Polynomial.C 1 : Polynomial O) 0
      = Polynomial.X + Polynomial.C 1 := by
  show (Polynomial.X + Polynomial.C 1 : Polynomial O) %ₘ (s2Key O) = _
  refine (Polynomial.modByMonic_eq_self_iff s2Key_monic).mpr ?_
  rw [s2Key_deg, Polynomial.degree_X_add_C]
  decide

include h2 hq in
theorem dvhgt_X1_zero :
    dvHgt (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O) 0 = (0 : ℕ∞) := by
  rw [dvHgt, key_eq h2 hq, dev_X1_zero h2 hq, KeyFrame.stageHeight_eq_inf]
  rw [Polynomial.natDegree_X_add_C, show Finset.range (1 + 1) = {0, 1} from rfl]
  simp only [Finset.inf_insert, Finset.inf_singleton, Polynomial.coeff_add,
    Polynomial.coeff_X_zero, Polynomial.coeff_X_one, Polynomial.coeff_C, gaussVal_C,
    e1_eq h2 hq, h_eq h2 hq]
  norm_num [addVal_one]

include h2 hq in
theorem dvhgt_X1_ge_one (j : ℕ) (hj : 1 ≤ j) :
    dvHgt (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O) j = ⊤ := by
  rw [dvHgt, key_eq h2 hq]
  have hz : dev (s2Key O) (Polynomial.X + Polynomial.C 1 : Polynomial O) j = 0 := by
    refine dev_eq_zero_of_lt s2Key_monic (by rw [s2Key_natDegree]; norm_num) _ _ ?_
    rw [Polynomial.natDegree_X_add_C, s2Key_natDegree]
    omega
  rw [hz]
  exact sh_zero h2 hq

/-! ## 5. The level-1 (5,2)-side data of the two digits -/

include h2 hq in
theorem dvsupp_D0 : dvSupp (s2Frame h2 hq) (D0 h2 hq) 5 2 = (13 : ℕ∞) := by
  rw [dvSupp, D0_natDegree h2 hq]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (by norm_num : (1 : ℕ) < 2 + 1))) ?_
    rw [dvhgt_D0_one h2 hq]
    decide
  · refine Finset.le_inf ?_
    intro j hj
    have hlt : j ≤ 2 := by
      have := Finset.mem_range.mp hj
      omega
    interval_cases j
    · refine le_trans (by decide : (13 : ℕ∞) ≤ 2 • (((7 : ℕ) : ℕ∞)) + (↑(5 : ℕ) * ↑(0 : ℕ))) ?_
      exact add_le_add (nsmul_le_nsmul_right (dvhgt_D0_zero_ge h2 hq) 2) le_rfl
    · rw [dvhgt_D0_one h2 hq]
      decide
    · simp [dvhgt_D0_ge_two h2 hq 2 le_rfl]

include h2 hq in
theorem dvside_D0_one_mem : 1 ∈ dvSideSet (s2Frame h2 hq) (D0 h2 hq) 5 2 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [D0_natDegree h2 hq]; norm_num),
    ?_, ?_⟩
  · rw [dvsupp_D0 h2 hq, dvhgt_D0_one h2 hq]
    decide
  · rw [dvhgt_D0_one h2 hq]
    decide

include h2 hq in
theorem hne_D0 : (dvSideSet (s2Frame h2 hq) (D0 h2 hq) 5 2).Nonempty :=
  ⟨1, dvside_D0_one_mem h2 hq⟩

include h2 hq in
theorem dvsidemin_D0 : dvSideMin (s2Frame h2 hq) (D0 h2 hq) 5 2 (hne_D0 h2 hq) = 1 := by
  classical
  refine le_antisymm (Finset.min'_le _ 1 (dvside_D0_one_mem h2 hq)) ?_
  refine Finset.le_min' _ _ _ ?_
  intro y hy
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
  have hon := (Finset.mem_filter.mp hy).2
  rw [D0_natDegree h2 hq] at hrange
  interval_cases y
  · -- `0` is NOT on the side: `13 = 2 • hgt₀` is impossible with `hgt₀ ≥ 7`
    exfalso
    have h13 := hon.1
    rw [dvsupp_D0 h2 hq] at h13
    have hge : (14 : ℕ∞) ≤ 2 • dvHgt (s2Frame h2 hq) (D0 h2 hq) 0 + (↑(5 : ℕ) * ↑(0 : ℕ)) := by
      refine le_trans (by decide : (14 : ℕ∞) ≤ 2 • (((7 : ℕ) : ℕ∞)) + (↑(5 : ℕ) * ↑(0 : ℕ))) ?_
      exact add_le_add (nsmul_le_nsmul_right (dvhgt_D0_zero_ge h2 hq) 2) le_rfl
    rw [← h13] at hge
    exact absurd hge (by decide)
  · norm_num
  · exact absurd (dvhgt_D0_ge_two h2 hq 2 le_rfl) hon.2

include h2 hq in
theorem dvsidemax_D0 : dvSideMax (s2Frame h2 hq) (D0 h2 hq) 5 2 (hne_D0 h2 hq) = 1 := by
  classical
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ 1 (dvside_D0_one_mem h2 hq))
  intro y hy
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
  have hon := (Finset.mem_filter.mp hy).2
  rw [D0_natDegree h2 hq] at hrange
  interval_cases y
  · norm_num
  · norm_num
  · exact absurd (dvhgt_D0_ge_two h2 hq 2 le_rfl) hon.2

include h2 hq in
theorem dvsidedeg_D0 : dvSideDeg (s2Frame h2 hq) (D0 h2 hq) 5 2 (hne_D0 h2 hq) = 0 := by
  rw [dvSideDeg, dvsidemax_D0 h2 hq, dvsidemin_D0 h2 hq]

include h2 hq in
theorem hp_D0 : dvHgt (s2Frame h2 hq) (D0 h2 hq)
    (dvSideMin (s2Frame h2 hq) (D0 h2 hq) 5 2 (hne_D0 h2 hq)) = ((4 : ℕ) : ℕ∞) := by
  rw [dvsidemin_D0 h2 hq, dvhgt_D0_one h2 hq]
  rfl

include h2 hq in
theorem dvsupp_X1 :
    dvSupp (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2 = (0 : ℕ∞) := by
  rw [dvSupp, Polynomial.natDegree_X_add_C]
  refine le_antisymm ?_ (by simp)
  refine le_trans (Finset.inf_le (Finset.mem_range.mpr (by norm_num : (0 : ℕ) < 1 + 1))) ?_
  rw [dvhgt_X1_zero h2 hq]
  decide

include h2 hq in
theorem dvside_X1_zero_mem :
    0 ∈ dvSideSet (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (by rw [Polynomial.natDegree_X_add_C]; norm_num), ?_, ?_⟩
  · rw [dvsupp_X1 h2 hq, dvhgt_X1_zero h2 hq]
    decide
  · rw [dvhgt_X1_zero h2 hq]
    decide

include h2 hq in
theorem hne_X1 :
    (dvSideSet (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2).Nonempty :=
  ⟨0, dvside_X1_zero_mem h2 hq⟩

include h2 hq in
theorem dvsidemin_X1 : dvSideMin (s2Frame h2 hq)
    (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2 (hne_X1 h2 hq) = 0 :=
  Nat.le_zero.mp (Finset.min'_le _ 0 (dvside_X1_zero_mem h2 hq))

include h2 hq in
theorem dvsidemax_X1 : dvSideMax (s2Frame h2 hq)
    (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2 (hne_X1 h2 hq) = 0 := by
  classical
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Nat.zero_le _)
  intro y hy
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
  have hon := (Finset.mem_filter.mp hy).2
  rw [Polynomial.natDegree_X_add_C] at hrange
  interval_cases y
  · norm_num
  · exact absurd (dvhgt_X1_ge_one h2 hq 1 le_rfl) hon.2

include h2 hq in
theorem dvsidedeg_X1 : dvSideDeg (s2Frame h2 hq)
    (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2 (hne_X1 h2 hq) = 0 := by
  rw [dvSideDeg, dvsidemax_X1 h2 hq, dvsidemin_X1 h2 hq]

include h2 hq in
theorem hp_X1 : dvHgt (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O)
    (dvSideMin (s2Frame h2 hq) (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2
      (hne_X1 h2 hq)) = ((0 : ℕ) : ℕ∞) := by
  rw [dvsidemin_X1 h2 hq, dvhgt_X1_zero h2 hq]
  rfl

/-! ## 6. `dv2Res` pinned, and its two values `1, 1` (the q = 2 collapse in `K₂`) -/

/-- **the `Exists.choose` resolution for `dv2Res`** — the M₀ pinned by C.38a's guard equation
is unique (`Nat.cast` injectivity on `ℕ∞`), so `dv2Res` may be read at ANY caller-supplied
pinning data.  This is exactly the "lemma nobody has stated" of C.38a's design docstring. -/
theorem dv2Res_pinned {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (L : LevelDatum F H₀ hpin) (A : Polynomial O)
    (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M₀ : ℕ∞)) :
    dv2Res L A = AdjoinRoot.mk L.r (dvResPoly F H₀ hpin A L.u L.ℓ hne M₀ hp) := by
  have hex : ∃ (hne' : (dvSideSet F A L.u L.ℓ).Nonempty) (M' : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne') = (M' : ℕ∞) := ⟨hne, M₀, hp⟩
  rw [dv2Res, dif_pos hex]
  congr 1
  have hM : hex.choose_spec.choose = M₀ := by
    have h1 : dvHgt F A (dvSideMin F A L.u L.ℓ hex.choose)
        = (hex.choose_spec.choose : ℕ∞) := hex.choose_spec.choose_spec
    have h2' : (hex.choose_spec.choose : ℕ∞) = (M₀ : ℕ∞) := h1.symm.trans hp
    exact_mod_cast h2'
  have hgen : ∀ (hne' : (dvSideSet F A L.u L.ℓ).Nonempty) (M' : ℕ)
      (hp' : dvHgt F A (dvSideMin F A L.u L.ℓ hne') = (M' : ℕ∞)), M' = M₀ →
      dvResPoly F H₀ hpin A L.u L.ℓ hne' M' hp' = dvResPoly F H₀ hpin A L.u L.ℓ hne M₀ hp := by
    rintro hne' M' hp' rfl
    rfl
  exact hgen _ _ _ hM

include h2 hq in
theorem dv2Res_D0 : dv2Res ((s2Tower h2 hq).levelDatum h2) (D0 h2 hq) = 1 := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  rw [dv2Res_pinned ((s2Tower h2 hq).levelDatum h2) (D0 h2 hq) (hne_D0 h2 hq) 4 (hp_D0 h2 hq)]
  show AdjoinRoot.mk ((s2Tower h2 hq).levelDatum h2).r
    (dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (D0 h2 hq) 5 2 (hne_D0 h2 hq) 4
      (hp_D0 h2 hq)) = 1
  have hspec := natDegree_dvResPoly (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq)
    (by norm_num : 0 < 2) (by decide : Nat.Coprime 5 2) (hne_D0 h2 hq) (hp_D0 h2 hq)
  rw [dvsidedeg_D0 h2 hq] at hspec
  rw [Polynomial.eq_C_of_natDegree_eq_zero hspec.1,
    eq_one_of_card_two (card_K₁ h2 hq) hspec.2, map_one, map_one]

include h2 hq in
theorem dv2Res_X1 : dv2Res ((s2Tower h2 hq).levelDatum h2)
    (Polynomial.X + Polynomial.C 1 : Polynomial O) = 1 := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  rw [dv2Res_pinned ((s2Tower h2 hq).levelDatum h2) _ (hne_X1 h2 hq) 0 (hp_X1 h2 hq)]
  show AdjoinRoot.mk ((s2Tower h2 hq).levelDatum h2).r
    (dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq)
      (Polynomial.X + Polynomial.C 1 : Polynomial O) 5 2 (hne_X1 h2 hq) 0 (hp_X1 h2 hq)) = 1
  have hspec := natDegree_dvResPoly (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq)
    (by norm_num : 0 < 2) (by decide : Nat.Coprime 5 2) (hne_X1 h2 hq) (hp_X1 h2 hq)
  rw [dvsidedeg_X1 h2 hq] at hspec
  rw [Polynomial.eq_C_of_natDegree_eq_zero hspec.1,
    eq_one_of_card_two (card_K₁ h2 hq) hspec.2, map_one, map_one]

/-! ## 7. The dv2-polygon of `f₅` at `Φ₂`: pins `(13, 0, ⊤, …)`, the side `(13, 1) = {0, 1}` -/

include h2 hq in
theorem dv2Pin_f₅_zero : dv2Pin ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 0 = (13 : ℕ∞) := by
  rw [dv2Pin, dev₂_f₅_zero h2 hq, dv2Hgt]
  exact dvsupp_D0 h2 hq

include h2 hq in
theorem dv2Pin_f₅_one : dv2Pin ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 1 = (0 : ℕ∞) := by
  rw [dv2Pin, dev₂_f₅_one h2 hq, dv2Hgt]
  exact dvsupp_X1 h2 hq

include h2 hq in
theorem dv2Pin_f₅_ge_two (j : ℕ) (hj : 2 ≤ j) :
    dv2Pin ((s2Tower h2 hq).levelDatum h2) (composedKey (s2Tower h2 hq)) (f₅ O) j = ⊤ := by
  rw [dv2Pin, dev₂_f₅_ge_two h2 hq j hj, dv2Hgt, dvSupp]
  rw [Polynomial.natDegree_zero, show Finset.range (0 + 1) = {0} from rfl]
  rw [Finset.inf_singleton]
  have hz : dvHgt (s2Frame h2 hq) (0 : Polynomial O) 0 = ⊤ := by
    rw [dvHgt, key_eq h2 hq]
    rw [show dev (s2Key O) (0 : Polynomial O) 0 = (0 : Polynomial O) %ₘ s2Key O from rfl,
      Polynomial.zero_modByMonic]
    exact sh_zero h2 hq
  rw [show ((s2Tower h2 hq).levelDatum h2).ℓ = 2 from rfl, hz, two_nsmul, top_add, top_add]

include h2 hq in
theorem dv2supp_f₅ : dv2Supp ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 = (13 : ℕ∞) := by
  rw [dv2Supp, f₅_natDegree]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (by norm_num : (0 : ℕ) < 5 + 1))) ?_
    rw [dv2Pin_f₅_zero h2 hq]
    decide
  · refine Finset.le_inf ?_
    intro j hj
    have hlt : j ≤ 5 := by
      have := Finset.mem_range.mp hj
      omega
    interval_cases j
    · rw [dv2Pin_f₅_zero h2 hq]; decide
    · rw [dv2Pin_f₅_one h2 hq]; decide
    · simp [dv2Pin_f₅_ge_two h2 hq 2 (by norm_num)]
    · simp [dv2Pin_f₅_ge_two h2 hq 3 (by norm_num)]
    · simp [dv2Pin_f₅_ge_two h2 hq 4 (by norm_num)]
    · simp [dv2Pin_f₅_ge_two h2 hq 5 (by norm_num)]

include h2 hq in
theorem dv2side_f₅_zero_mem : 0 ∈ dv2SideSet ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [f₅_natDegree]; norm_num),
    ?_, ?_⟩
  · rw [dv2supp_f₅ h2 hq, dv2Pin_f₅_zero h2 hq]
    decide
  · rw [dv2Pin_f₅_zero h2 hq]
    decide

include h2 hq in
theorem dv2side_f₅_one_mem : 1 ∈ dv2SideSet ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [f₅_natDegree]; norm_num),
    ?_, ?_⟩
  · rw [dv2supp_f₅ h2 hq, dv2Pin_f₅_one h2 hq]
    decide
  · rw [dv2Pin_f₅_one h2 hq]
    decide

include h2 hq in
/-- ★ **NODE C.78's `hne₃` is INHABITED** — the first dv2-level side of a probe at a composed
key in the corpus. -/
theorem hne₃_f₅ : (dv2SideSet ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1).Nonempty :=
  ⟨0, dv2side_f₅_zero_mem h2 hq⟩

include h2 hq in
theorem dv2sidemin_f₅ : dv2SideMin ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 (hne₃_f₅ h2 hq) = 0 :=
  Nat.le_zero.mp (Finset.min'_le _ 0 (dv2side_f₅_zero_mem h2 hq))

include h2 hq in
theorem dv2sidemax_f₅ : dv2SideMax ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 (hne₃_f₅ h2 hq) = 1 := by
  classical
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ 1 (dv2side_f₅_one_mem h2 hq))
  intro y hy
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
  have hon := (Finset.mem_filter.mp hy).2
  rw [f₅_natDegree] at hrange
  interval_cases y
  · norm_num
  · norm_num
  · exact absurd (dv2Pin_f₅_ge_two h2 hq 2 (by norm_num)) hon.2
  · exact absurd (dv2Pin_f₅_ge_two h2 hq 3 (by norm_num)) hon.2
  · exact absurd (dv2Pin_f₅_ge_two h2 hq 4 (by norm_num)) hon.2
  · exact absurd (dv2Pin_f₅_ge_two h2 hq 5 (by norm_num)) hon.2

include h2 hq in
theorem dv2sidedeg_f₅ : dv2SideDeg ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 (hne₃_f₅ h2 hq) = 1 := by
  rw [dv2SideDeg, dv2sidemax_f₅ h2 hq, dv2sidemin_f₅ h2 hq]

/-! ## 8. The level-2 residual is `X + 1` — separable, with its own monic irreducible divisor -/

include h2 hq in
/-- ★ **the level-2 residual of the probe**: `dv2ResPoly = X + 1` over
`K₂ = AdjoinRoot (towerLabel s2Tower)` — both slot reads collapse to `1` (q = 2). -/
theorem dv2respoly_f₅ : dv2ResPoly ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 (hne₃_f₅ h2 hq)
      = Polynomial.X + 1 := by
  rw [dv2ResPoly, dv2sidedeg_f₅ h2 hq, dv2sidemin_f₅ h2 hq]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num
  rw [dev₂_f₅_zero h2 hq, dev₂_f₅_one h2 hq, dv2Res_D0 h2 hq, dv2Res_X1 h2 hq, map_one]
  ring

include h2 hq in
theorem dv2respoly_f₅_separable : (dv2ResPoly ((s2Tower h2 hq).levelDatum h2)
    (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 (hne₃_f₅ h2 hq)).Separable := by
  rw [dv2respoly_f₅ h2 hq]
  exact ⟨0, 1, by simp⟩

include h2 hq in
theorem r₂_monic : (Polynomial.X + 1 :
    Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq)))).Monic := by
  rw [show (1 : Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq))))
    = Polynomial.C 1 from (Polynomial.C_1).symm]
  exact Polynomial.monic_X_add_C 1

include h2 hq in
theorem r₂_natDegree : (Polynomial.X + 1 :
    Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq)))).natDegree = 1 := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  haveI : Fact (Irreducible (towerLabel (s2Tower h2 hq))) :=
    ⟨(towerLabel_spec (s2Tower h2 hq) h2).2.1⟩
  rw [show (1 : Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq))))
    = Polynomial.C 1 from (Polynomial.C_1).symm]
  exact Polynomial.natDegree_X_add_C 1

include h2 hq in
theorem r₂_irreducible : Irreducible (Polynomial.X + 1 :
    Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq)))) := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  haveI : Fact (Irreducible (towerLabel (s2Tower h2 hq))) :=
    ⟨(towerLabel_spec (s2Tower h2 hq) h2).2.1⟩
  have h : (Polynomial.X + 1 : Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq))))
      = Polynomial.X - Polynomial.C (-1) := by
    rw [map_neg, sub_neg_eq_add, Polynomial.C_1]
  rw [h]
  exact Polynomial.irreducible_X_sub_C (-1)

include h2 hq in
theorem r₂_dvd : (Polynomial.X + 1 : Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq))))
    ∣ dv2ResPoly ((s2Tower h2 hq).levelDatum h2)
        (composedKey (s2Tower h2 hq)) (f₅ O) 13 1 (hne₃_f₅ h2 hq) := by
  rw [dv2respoly_f₅ h2 hq]
  exact dvd_rfl

include h2 hq in
/-- the seam floor holds strictly: `ℓ₃ · E₂ = 10 < 13 = u₃`. -/
theorem hfloor₃_f₅ : 1 * (s2Tower h2 hq).E₂ < 13 := by
  rw [(s2Tower_data h2 hq).2.2.2.2]
  norm_num

/-! ## 9. The Hensel witness: `f₅` has a root, hence a monic degree-4 divisor -/

include h2 hq in
private theorem f₅_explicit : (f₅ O)
    = Polynomial.X ^ 5 + Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X ^ 3
      - Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X
      + Polynomial.C 12 := by
  rw [f₅, s2Key]
  simp only [map_ofNat, map_one]
  ring

include h2 hq in
private theorem f₅_eval_three : (f₅ O).eval 3 = 216 := by
  rw [f₅_explicit h2 hq]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  norm_num

include h2 hq in
private theorem f₅_deriv_eval_three : (f₅ O).derivative.eval 3 = 389 := by
  rw [f₅_explicit h2 hq]
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
    zero_mul, mul_one, zero_add, add_zero]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

include h2 hq in
theorem exists_root_f₅ [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    ∃ z : O, (f₅ O).IsRoot z := by
  have heval : (f₅ O).eval 3 ∈ IsLocalRing.maximalIdeal O := by
    rw [f₅_eval_three h2 hq, show (216 : O) = 2 * 108 by norm_num]
    exact Ideal.mul_mem_right _ _ (two_mem_max h2)
  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
      ((f₅ O).derivative.eval 3)) := by
    rw [f₅_deriv_eval_three h2 hq, show (389 : O) = 2 * 194 + 1 by norm_num, map_add,
      map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (two_mem_max h2), zero_mul,
      zero_add]
    exact isUnit_one
  obtain ⟨z, hz, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O)
    (f₅ O) f₅_monic 3 heval hunit
  exact ⟨z, hz⟩

include h2 hq in
/-- ★ **the exact-degree witness exists**: a monic degree-4 divisor of
`blockFactor (levelDatum) f₅ = f₅` — the Hensel cofactor of the odd root. -/
theorem exists_monic_deg_four_divisor [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    ∃ g : Polynomial O, g.Monic ∧
      g ∣ blockFactorLeaky ((s2Tower h2 hq).levelDatum h2) (f₅ O) ∧ g.natDegree = 4 := by
  obtain ⟨z, hz⟩ := exists_root_f₅ h2 hq
  have hfact : (Polynomial.X - Polynomial.C z) * ((f₅ O) /ₘ (Polynomial.X - Polynomial.C z))
      = f₅ O := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hz
  have hgm : ((f₅ O) /ₘ (Polynomial.X - Polynomial.C z)).Monic :=
    (Polynomial.monic_X_sub_C z).of_mul_monic_left (hfact.symm ▸ f₅_monic (O := O))
  have hdeg : ((f₅ O) /ₘ (Polynomial.X - Polynomial.C z)).natDegree = 4 := by
    have hd := congrArg Polynomial.natDegree hfact
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero z) hgm.ne_zero,
      Polynomial.natDegree_X_sub_C, f₅_natDegree] at hd
    omega
  refine ⟨(f₅ O) /ₘ (Polynomial.X - Polynomial.C z), hgm, ?_, hdeg⟩
  rw [blockFactor_f₅ h2 hq]
  exact ⟨Polynomial.X - Polynomial.C z, by rw [mul_comm]; exact hfact.symm⟩

/-! ## 10. ★ THE ADJUDICATION THEOREM — C.78's core fires at the probe

The signed statement's conclusion, first three conjuncts, at the instantiated composite
degree `(F.e₁ · T.e₂ · ℓ₃) · (F.f₁ · T.f₂ · deg r₂)` with `(u₃, ℓ₃, r₂) = (13, 1, X + 1)`:
every hypothesis of `partial_block_decision` holds at this instance (§§7–8 above +
`blockContext_f₅`), and the exact-degree existential is TRUE — at the very probe where the
same demand read on the BLOCK (C.77 (iii), C.80) was machine-refuted (`5 = 4`).  The
conditional `typeOf` clause for this witness is numerically certified TRUE (module
docstring) and left as named open Lean work — it is NOT claimed by this theorem. -/

include h2 hq in
theorem partialBlockDecision_core_at_probe [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    ∃ g : Polynomial O, g.Monic ∧
      g ∣ blockFactorLeaky ((s2Tower h2 hq).levelDatum h2) (f₅ O) ∧
      g.natDegree = ((s2Frame h2 hq).e₁ * (s2Tower h2 hq).e₂ * 1)
        * ((s2Frame h2 hq).f₁ * (s2Tower h2 hq).f₂
            * (Polynomial.X + 1 :
                Polynomial (AdjoinRoot (towerLabel (s2Tower h2 hq)))).natDegree) := by
  obtain ⟨g, hgm, hdvd, hdeg⟩ := exists_monic_deg_four_divisor h2 hq
  refine ⟨g, hgm, hdvd, ?_⟩
  rw [r₂_natDegree h2 hq, e1_eq h2 hq, f1_eq h2 hq,
    show (s2Tower h2 hq).e₂ = 2 from rfl, show (s2Tower h2 hq).f₂ = 1 from rfl, hdeg]

/-! ## 11. The ∀-closure Prop carrier (C.61's `Tier1TypeOfStatement` precedent)

The exact signed type of NODE C.78, closed over everything, so future units (the order-2
dictionary carrier, or a refutation attempt at a different probe) can name it.  NOT proved,
NOT refuted, NOT declared as an axiom here. -/

/-- The signed C.78 `partial_block_decision`, closed over everything. -/
def PartialBlockDecisionStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O)
    (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (f : Polynomial O) (_hctx : BlockContext (T.levelDatum hπ) f)
    (u₃ ℓ₃ : ℕ) (_hℓ₃ : 0 < ℓ₃) (_hcop₃ : Nat.Coprime u₃ ℓ₃) (_hfloor₃ : ℓ₃ * T.E₂ < u₃)
    (hne₃ : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty)
    (_hsep : (dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃).Separable)
    (r₂ : Polynomial (AdjoinRoot (towerLabel T))) (_hr₂m : r₂.Monic)
    (_hr₂i : Irreducible r₂)
    (_hdvd : r₂ ∣ dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃),
    ∃ g : Polynomial O, g.Monic ∧ g ∣ blockFactor (T.levelDatum hπ) f ∧
      g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
      ((∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g') →
       (∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * r₂.natDegree) ∣ inertiaDegOf g') →
        typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩ ∧ Irreducible g)

end Uniformity.Density.Tower.C78adj

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C78adj.slotIdx_five
#print axioms Uniformity.Density.Tower.C78adj.composedKey_s2Tower
#print axioms Uniformity.Density.Tower.C78adj.isUnit_entryW
#print axioms Uniformity.Density.Tower.C78adj.dev₂_f₅_zero
#print axioms Uniformity.Density.Tower.C78adj.dv2Pin_f₅_zero
#print axioms Uniformity.Density.Tower.C78adj.dv2Res_pinned
#print axioms Uniformity.Density.Tower.C78adj.hne₃_f₅
#print axioms Uniformity.Density.Tower.C78adj.dv2respoly_f₅
#print axioms Uniformity.Density.Tower.C78adj.dv2respoly_f₅_separable
#print axioms Uniformity.Density.Tower.C78adj.r₂_monic
#print axioms Uniformity.Density.Tower.C78adj.r₂_natDegree
#print axioms Uniformity.Density.Tower.C78adj.r₂_irreducible
#print axioms Uniformity.Density.Tower.C78adj.r₂_dvd
#print axioms Uniformity.Density.Tower.C78adj.hfloor₃_f₅
#print axioms Uniformity.Density.Tower.C78adj.dv2sidedeg_f₅
#print axioms Uniformity.Density.Tower.C78adj.exists_root_f₅
#print axioms Uniformity.Density.Tower.C78adj.exists_monic_deg_four_divisor
#print axioms Uniformity.Density.Tower.C78adj.partialBlockDecision_core_at_probe
#print axioms Uniformity.Density.Tower.C78adj.PartialBlockDecisionStatement

end AxCheck
