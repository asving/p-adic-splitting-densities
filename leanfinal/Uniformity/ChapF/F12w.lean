/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F12
import Uniformity.ChapF.F02
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapF.F12w — the W-1 transport at the carrier vocabulary (HYP.139, proved layer)

**An F.12-adjacent appendix file, not a blueprint node** (the H09w/H89w/H73w precedent;
registered by blueprint AMENDMENT A-W.2, 2026-08-16, unit OM-9). HYP.139 is MATH-classed:
"Transport of the harness w and 𝑅 to the FGMN objects is still W-1 (ATTEMPT) — and the
corpus's own march-level dictionary for that transport, TR-3′-GEN, is OPEN at general
order." This file proves everything the LANDED CARRIER can carry, certified before proving
by `verification/openmath/om9_weld_cert.py` LEG B (exhaustive at `|ι| = 3` over F₃/F₄ with
the exact count `((q−1)²+1)³`; the ω-cocycle law over all `(Kˣ)^{ℤ/6}` at three fields with
`#{ω ≡ 1} = gcd(6, q−1)` exactly; the ω-vs-ω⁻¹ involution separator).

* `w1Transport_iff_slotScale` — the carrier is an ORBIT relation of F.01's gauge action:
  the two surviving weld conjuncts (HYP.74's slot leg and HYP.139's transport) ride the
  same `slotScale` mechanism.
* `w1Transport_iff_zero_iff` — **the characterization**: over a field the carrier's
  existential is EQUIVALENT to equality of vanishing loci. This is the machine-checked form
  of the blueprint's own FAITHFULNESS disclosure ("the ι-indexed shape is the transport's
  SIGNATURE only"): everything beyond matching zero-sets — TR-3′-GEN's compatible dictionary
  at general order — lives in the SITE INSTANTIATION, not in the carrier. Consequently
  chapter I's `w1` field is dischargeable at any site whose two residual families are
  pointwise nonvanishing (`w1Transport_of_ne_zero`), and HYP.139's MATH content is exactly
  what such a discharge would NOT prove.
* `w1Transport_refl/symm/trans` — the transport is an equivalence relation (instant from
  the characterization).
* `lineCobdry` + `lineCobdry_cocycle` + `lineCobdry_eq_one_iff` — the (DMULT-w) mechanism
  (`EFF.GRTJC.69`): a line-wise unit system prices `ω(λ,μ) = c_{λ+μ}/(c_λ c_μ)`, "the
  2-coboundary of the line-wise unit system"; ω always satisfies the `Kˣ`-valued 2-cocycle
  law, and `ω ≡ 1` iff the system is additive-to-multiplicative — the machine form of
  "That ω depends only on the lines is what the transport gives; **nothing gives ω ≡ 1**."
  A concrete `ω ≠ 1` witness is the closing example.

**What stays MATH (HYP.139 unchanged, WELD-ZERO fence untouched):** nothing here
instantiates the carrier at the GENHN-4 site, and nothing here consumes or anticipates the
pending WELD-ZERO arc (honesty F-2; clean-pass 1 of 2 at HEAD).
-/

namespace Uniformity.Density.Weld

variable {K : Type*} [Field K] {ι : Type*}

/-- The W-1 carrier is the `slotScale` ORBIT relation: `Rh` is a gauge transform of `RG`
by F.01's slot action. One mechanism under both surviving weld conjuncts. -/
theorem w1Transport_iff_slotScale (Rh RG : ι → K) :
    W1Transport Rh RG ↔ ∃ c : ι → Kˣ, Rh = slotScale c RG := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, funext hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun l => congrFun hc l⟩

/-- **The characterization**: over a field, the abstract W-1 carrier holds iff the two
families have EQUAL VANISHING LOCI. Certified exhaustively (om9_weld_cert.py LEG B1, count
`((q−1)²+1)³` exact at F₃ and F₄) before proving. -/
theorem w1Transport_iff_zero_iff (Rh RG : ι → K) :
    W1Transport Rh RG ↔ ∀ l, Rh l = 0 ↔ RG l = 0 := by
  constructor
  · rintro ⟨c, hc⟩ l
    rw [hc l]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h (Units.ne_zero (c l))
      · exact h
    · intro h
      rw [h, mul_zero]
  · intro hloci
    classical
    have key : ∀ l, ∃ cl : Kˣ, Rh l = (cl : K) * RG l := by
      intro l
      by_cases h : RG l = 0
      · exact ⟨1, by rw [h, mul_zero]; exact (hloci l).mpr h⟩
      · have hR : Rh l ≠ 0 := fun hh => h ((hloci l).mp hh)
        exact ⟨Units.mk0 (Rh l / RG l) (div_ne_zero hR h), by
          rw [Units.val_mk0, div_mul_cancel₀ _ h]⟩
    choose c hc using key
    exact ⟨c, hc⟩

theorem w1Transport_refl (Rh : ι → K) : W1Transport Rh Rh :=
  (w1Transport_iff_zero_iff Rh Rh).mpr fun _ => Iff.rfl

theorem w1Transport_symm {Rh RG : ι → K} (h : W1Transport Rh RG) : W1Transport RG Rh :=
  (w1Transport_iff_zero_iff RG Rh).mpr fun l =>
    ((w1Transport_iff_zero_iff Rh RG).mp h l).symm

theorem w1Transport_trans {R1 R2 R3 : ι → K} (h12 : W1Transport R1 R2)
    (h23 : W1Transport R2 R3) : W1Transport R1 R3 :=
  (w1Transport_iff_zero_iff R1 R3).mpr fun l =>
    ((w1Transport_iff_zero_iff R1 R2).mp h12 l).trans
      ((w1Transport_iff_zero_iff R2 R3).mp h23 l)

/-- The discharge shape at nonvanishing sites: two pointwise-nonvanishing families are
always W-1-transportable at the carrier level. (What this does NOT prove: TR-3′-GEN's
compatible dictionary — HYP.139's MATH content.) -/
theorem w1Transport_of_ne_zero {Rh RG : ι → K} (h1 : ∀ l, Rh l ≠ 0)
    (h2 : ∀ l, RG l ≠ 0) : W1Transport Rh RG :=
  (w1Transport_iff_zero_iff Rh RG).mpr fun l =>
    ⟨fun h => absurd h (h1 l), fun h => absurd h (h2 l)⟩

/-- Mismatched vanishing loci refuse every transport — the constructed-counterexample leg
as a fact (om9_weld_cert.py LEG B1's negative side). -/
example : ¬ W1Transport (fun _ : Fin 1 => (1 : ZMod 3)) fun _ => (0 : ZMod 3) := by
  rw [w1Transport_iff_zero_iff]
  intro h
  exact one_ne_zero ((h 0).mpr rfl)

/-- The (DMULT-w) coboundary of a line-wise unit system (`EFF.GRTJC.69`):
`ω(l,m) = c(l+m)·(c_l·c_m)⁻¹`. -/
def lineCobdry [Add ι] (c : ι → Kˣ) : ι → ι → Kˣ :=
  fun l m => c (l + m) * (c l * c m)⁻¹

/-- ω is ALWAYS a `Kˣ`-valued 2-cocycle (om9_weld_cert.py LEG B3: all `(Kˣ)^{ℤ/6}` systems
at F₃/F₄/F₅) — the mechanism by which a W-1 unit system feeds F.07's cocycle class. -/
theorem lineCobdry_cocycle [AddSemigroup ι] (c : ι → Kˣ) (a b d : ι) :
    lineCobdry c a b * lineCobdry c (a + b) d
      = lineCobdry c b d * lineCobdry c a (b + d) := by
  show c (a + b) * (c a * c b)⁻¹ * (c (a + b + d) * (c (a + b) * c d)⁻¹)
      = c (b + d) * (c b * c d)⁻¹ * (c (a + (b + d)) * (c a * c (b + d))⁻¹)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_mul_div_comm, div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  apply Units.ext
  push_cast
  simp only [add_assoc]
  ring

/-- "Nothing gives ω ≡ 1": the coboundary is trivial exactly when the line system is a
homomorphism of the line addition into `Kˣ` (om9_weld_cert.py LEG B3: exactly
`gcd(6, q−1)` of the `(q−1)⁶` systems at `ι = ℤ/6`). -/
theorem lineCobdry_eq_one_iff [Add ι] (c : ι → Kˣ) :
    (∀ l m, lineCobdry c l m = 1) ↔ ∀ l m, c (l + m) = c l * c m := by
  constructor <;> intro h l m
  · have hh := h l m
    rw [lineCobdry, mul_inv_eq_one] at hh
    exact hh
  · show c (l + m) * (c l * c m)⁻¹ = 1
    rw [h l m]
    exact mul_inv_cancel _

/-- A concrete `ω ≠ 1` witness (`ι = ℤ/2`, `K = F₃`): the corpus's "nothing gives ω ≡ 1",
instantiated. -/
example :
    lineCobdry (fun l : ZMod 2 => if l = 0 then (-1 : (ZMod 3)ˣ) else 1) 1 1 ≠ 1 := by
  decide

end Uniformity.Density.Weld
