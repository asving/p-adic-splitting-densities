/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D47
import Uniformity.ChapD.D48

/-!
# Uniformity.ChapD.D49 — LEMMA T4.2(a): exact attainment for the key power

**Chapter D, NODE D.49** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the
certificate witness (T4); amendments A-1, A-D.1 govern — this node's signature is unamended).
ENVIRONMENT: as D.46 (ENV-D3 plus the two extra parameters `(Dv, Slot)`; binders inline, no
`variable` block — B.42). Two public declarations: the signed theorem and its signed sibling
corollary.

*Exact attainment.* For a certificate frame `F` (D.46) and a coordinate `j < μ₂`,

```
Touched F j  ↔  ν_j(f_key) = Θ_j                    (touched_iff_nu_eq)
¬ Touched F j  →  Θ_j < ν_j(f_key)                  (nu_gt_of_untouched)
```

with `ν` the totalized first-discrepancy height of D.47 and `Touched` D.48's `ω_j ≠ 0`. The
second display is `EFF.T4.14`'s "at an untouched coordinate `ν_j(f_key) > Θ_j`, **where
`+∞ > Θ_j` includes the case of an identically zero discrepancy**" — the `⊤` branch of `ν` needs
no separate clause, which is exactly what D.47's totalization was for.

## The route (`EFF.T4.14`'s three steps, verbatim in substance)

1. **(FLOOR) gives the lower bound.** Specializing D.46's `floor` field at `fkey_mem` and `hj`:
   `grΔ m j f_key = 0` for every `m < Θ_j`. So every element of D.47's set is `≥ Θ_j`, and
   `le_sInf` turns that into `Θ_j ≤ ν_j(f_key)`.
2. **Equality holds iff `Θ_j` is itself in the set.** Forward: if `ω_j ≠ 0` then `Θ_j` IS a
   member (`ω_j = grΔ (Θ_j) j f_key` definitionally, D.48), so `sInf_le` gives the reverse
   inequality and `le_antisymm` closes it. Backward: if `ω_j = 0` then step 1 sharpens — every
   member is `≥ Θ_j` and `≠ Θ_j`, hence `≥ Θ_j + 1` — so `ν_j(f_key) ≥ Θ_j + 1`, contradicting
   `ν_j(f_key) = Θ_j`.
3. **The untouched corollary** is that sharpened bound read as a strict inequality:
   `Θ_j < Θ_j + 1 ≤ ν_j(f_key)`, and when the discrepancy is identically zero D.47's set is
   EMPTY, `ν_j(f_key) = ⊤`, and the same `le_sInf` step delivers `⊤` with no case split.

The two `le_sInf` bounds are shared by both public declarations and are factored out as the two
`private` helpers `CertFrame.theta_le_nuIdx` and `CertFrame.succ_theta_le_nuIdx`. Nothing is
signed at those names; they exist so that the sharpened bound is written once.

## Faithfulness

**`hj : j < F.μ₂` is necessary, not decoration.** It is the only route to (FLOOR), and without
it the FORWARD direction is false: take a frame whose `Θ` is `5` at some `j ≥ μ₂` with
`grΔ 5 j f_key ≠ 0` and also `grΔ 3 j f_key ≠ 0`. Then `Touched j` holds while
`ν_j(f_key) = 3 ≠ 5 = Θ_j`. The corpus quantifies T4.2(a) over the coordinate range and so does
this statement.

**The statement is about `f_key` ALONE — no member-general converse is inferred.** S8 PE1(2)'s
check ("uses the GENTOW-3 floor and does not infer a member-general converse") is scored by the
signature: `nuIdx j F.fkey`, not `nuIdx j f` for `f ∈ F.M`. The no-converse warning itself is
D.52's ⚠(ii) and `EFF.T4.19`'s fence at D.53 — entry-driven content of ANOTHER member may still
attain `Θ_j` while `ω_j = 0`, and nothing in this file says otherwise.

**`Touched` and `ω_j` are used through their definitions, not through extra hypotheses.**
`F.Touched j` is `F.omega j ≠ 0` is `F.grΔ (F.Θ j) j F.fkey ≠ 0` — the two unfoldings are
definitional (D.48), which is why step 2's membership witness is literally `⟨F.Θ j, rfl, ht⟩`.

**No new definition** — nothing is added to the trust boundary here beyond D.46/D.47/D.48's own
flagged definitions.

**Non-vacuity is NOT re-executed here.** `CertFrame` is inhabited with (FLOOR) satisfied AND
coordinate `j = 0` touched, so this equivalence is not vacuous; that witness is D.68's census
row (A-D.1 addition (v)) and duplicating it here would put two copies of one battery row in the
chapter.

DEPENDS: D.46 (`CertFrame`, its `floor`/`fkey_mem` fields), D.47 (`CertFrame.nuIdx`), D.48
(`CertFrame.omega`, `CertFrame.Touched`) — all landed at `Uniformity.ChapD.D46`/`D47`/`D48` ·
mathlib `le_sInf`, `sInf_le`, `le_antisymm`, `lt_of_lt_of_le`, `not_not`, and the `ℕ → ℕ∞` cast
lemmas reached by `exact_mod_cast`. Not D.45: the thresholds enter only through the frame's own
`Θ` field.

SOURCE: `EFF.T4.14` (the statement and its three-step proof; "including the identically-zero
case through the convention `ν_j(f_key) = +∞`").

**TEETH.** S8 PE1(2) → **this Lean theorem**. The no-converse half of that check is a fence, not
a claim, and is carried in the faithfulness note above (and at D.52/D.53). Gate D.66 leg 4 runs
the FR-M3 numerals — `Θ = [10,7,4]`, self-shadow pins `[12,7,4]`, so `ν₀ = 12 > 10 = Θ₀`
(untouched with slack) while `j = 1,2` attain — as `ℕ∞` facts; those numerals are the gate's, not
duplicated here.

ENVIRONMENT: as D.46 — ENV-D3 (`[Field K]` for the digit field) plus `(Dv, Slot)`, written inline
as each declaration's own binders.

## Status

Sorry-free, axiom-free (Lean core only): both declarations are PROVED theorems here, not the
leanspec `axiom` stubs.
-/

namespace Uniformity.Density.Gauge

/-- (FLOOR) as a lower bound on the first-discrepancy height of the key power: every height
carrying a nonzero assembled digit is at least `Θ_j`.  Step 1 of `EFF.T4.14`; `private`, shared
by the two signed declarations below. -/
private theorem CertFrame.theta_le_nuIdx {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) :
    (F.Θ j : ℕ∞) ≤ F.nuIdx j F.fkey := by
  refine le_sInf ?_
  intro m hm
  obtain ⟨m', rfl, hm'⟩ := hm
  have hle : F.Θ j ≤ m' := by
    by_contra hlt
    exact hm' (F.floor F.fkey F.fkey_mem j hj m' (by omega))
  exact_mod_cast hle

/-- The sharpened bound at an untouched coordinate: with the height-`Θ_j` digit itself zero,
every nonzero digit sits at height `≥ Θ_j + 1`.  Step 2's backward half and step 3 of
`EFF.T4.14`; `private`.  When the discrepancy is identically zero the set is empty and `le_sInf`
returns `⊤` — the `+∞` branch, with no case split. -/
private theorem CertFrame.succ_theta_le_nuIdx {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) (hzero : F.omega j = 0) :
    ((F.Θ j + 1 : ℕ) : ℕ∞) ≤ F.nuIdx j F.fkey := by
  refine le_sInf ?_
  intro m hm
  obtain ⟨m', rfl, hm'⟩ := hm
  have hle : F.Θ j ≤ m' := by
    by_contra hlt
    exact hm' (F.floor F.fkey F.fkey_mem j hj m' (by omega))
  have hne : m' ≠ F.Θ j := by
    rintro rfl
    exact hm' hzero
  have hsucc : F.Θ j + 1 ≤ m' := by omega
  exact_mod_cast hsucc

/-- **D.49 — LEMMA T4.2(a): exact attainment for the key power** (`EFF.T4.14`).  On the
coordinate range `j < μ₂`, the coordinate is touched exactly when the key power's
first-discrepancy height is the threshold itself: `Touched j ↔ ν_j(f_key) = Θ_j`.
⚠ The statement is about `f_key` ALONE; no member-general converse is inferred (that fence is
D.52's ⚠(ii)). -/
theorem CertFrame.touched_iff_nu_eq {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) :
    F.Touched j ↔ F.nuIdx j F.fkey = (F.Θ j : ℕ∞) := by
  constructor
  · -- touched: `Θ_j` is a member of D.47's set, and (FLOOR) makes it the least one.
    intro ht
    exact le_antisymm (sInf_le ⟨F.Θ j, rfl, ht⟩) (F.theta_le_nuIdx hj)
  · -- untouched: every nonzero digit sits at `≥ Θ_j + 1`, so the height cannot BE `Θ_j`.
    intro heq hzero
    have hgt := F.succ_theta_le_nuIdx hj hzero
    rw [heq] at hgt
    have hcontra : F.Θ j + 1 ≤ F.Θ j := by exact_mod_cast hgt
    omega

/-- **D.49 — the untouched corollary** (`EFF.T4.14`).  At an untouched coordinate the key
power's first discrepancy is strictly above the threshold, `Θ_j < ν_j(f_key)`, "where
`+∞ > Θ_j` includes the case of an identically zero discrepancy" — the `⊤` value of D.47's
totalized `ν` satisfies this inequality with no separate clause. -/
theorem CertFrame.nu_gt_of_untouched {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) (hu : ¬ F.Touched j) :
    (F.Θ j : ℕ∞) < F.nuIdx j F.fkey := by
  have hzero : F.omega j = 0 := not_not.mp hu
  refine lt_of_lt_of_le ?_ (F.succ_theta_le_nuIdx hj hzero)
  exact_mod_cast Nat.lt_succ_self (F.Θ j)

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame.touched_iff_nu_eq
#print axioms Uniformity.Density.Gauge.CertFrame.nu_gt_of_untouched

end AxCheck
