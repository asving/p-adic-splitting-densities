/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D25a
import Uniformity.ChapD.D18

/-!
# Uniformity.ChapD.D28 — `(C3-level-1-key)`: the A3 pin, and the naive/corrected comparison

**Chapter D, NODE D.28** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer). The SIGNATURE is the **`[re-signed: A-D.1/D-D4 + D-D5 + D-D7]`** one — every `…`
elision expanded from this node's own STATEMENT text (§12 rule 5), `Module.Basis` at the v4.31.0
pin, `π` explicit and first, and the four type slips repaired; **no strength change**, the
hypotheses are the ones the STATEMENT already names. ENV-D4 + the `(K₁, η, b)` carrier data.
Three signed declarations.

*The setting.* A carrier `(K₁, η)` with an `F`-basis `b : Module.Basis (Fin f₁) F K₁`,
`b r = η^r` (the corpus's fixed basis `1, η, …, η^{f₁−1}`, `EFF.T1.01`), `F := ResidueField O`;
a slot `t < f₂` with `M_t := (f₂−t)·u₂ > D′h`, and a digit `c_t : F ⊆ K₁`.

1. **`levelOne_corrected_key`** — the corrected level-1 coefficient
   `k̂_t := liftC6 e₁ h σ M_t (b.repr (c_t · η^{W(t)}))`, i.e. the corpus's
   `k̂_t = L_{M_t}(c_t η^{W(t)})` on coordinates: `c_t ≠ 0 ⇒` exact height `M_t` (D.25),
   `c_t = 0 ⇒ k̂_t = 0` with valuation `⊤` (`hσ0` + `b.repr 0 = 0`) — the **A3 zero branch**.
2. **`levelOne_cmult`** — the multiplicative coefficient is exactly `c_t`:
   `(c_t·η^{W(t)})·η^{−W(t)} = c_t`, in `K₁ˣ`-form
   `Γ_t · ((levelOneArena …).vartheta u₂ (f₂−t))⁻¹ = c_t` by D.18 (the A3 display
   `c^mult = Γ_t η^{−W(t)} = c_t`).
3. **`levelOne_naive_agree_iff`** — naive/corrected agreement in slot `t` iff
   `c_t·(ϑ_{1,f₂−t} − 1) = 0` (`EFF.T1.13`'s criterion — over the field: iff
   `c_t = 0 ∨ η^{W(t)} = 1`).

## ⚠ Fragile signature, and D-D7's four type slips

The blueprint flags the `Module.Basis` + `repr` + `algebraMap` stack as fragile and records that
it was elaborated FIRST at the stub stage; the leanspec form is the elaboration, and this file
transcribes it byte-for-byte. The four slips D-D7 names — all repaired in the signature, none
mathematical, each one a debugging cycle saved:

1. `Wfloor` takes `u₂ : ℤ` while this node binds `u₂ : ℕ` → the cast `(u₂ : ℤ)` at every
   `Wfloor` occurrence (heights are `ℤ`, D.16);
2. `t : Fin f₂` is fed both to `Wfloor`'s `t : ℕ` and to `f₂ − t` → `(t : ℕ)` at both;
3. `b.repr (…)` is a `Finsupp` but `liftC6` wants `Fin f₁ → ResidueField O` → the coercion is
   written `fun r => b.repr (…) r`;
4. the section and positivity hypotheses were elided → expanded from the STATEMENT's own list.

`Module.Basis` (not bare `Basis`, which does not resolve at the pin) is D-D5.

## Faithfulness

Three recasts, flagged for the chapter cross-read (no new definition here — `liftC6` is D.24's
and `Wfloor` is D.16's, both already at the trust boundary):

* *`hb : ∀ r, b r = η^r` is signed but never consumed, and that is informative.* The height
  claim goes through `b.repr`'s injectivity alone, so it holds for **any** `F`-basis of `K₁`:
  what the corpus's fixed basis `1, η, …, η^{f₁−1}` fixes is the *meaning* of the coordinates
  (which is why the A3 display can read `c^mult` off slot `0`), not the exactness of the height.
  The binder is kept — the statement is landed byte-for-byte and is not weakened — and marked
  with `set_option linter.unusedVariables false in` rather than deleted.
* *`hh : 0 < h` is likewise inert here.* It is D.25's carried ⚠ hypothesis (§14 item 5), and
  D.25's own clause-1 note already records that the `h = 0` corner needs no extra hypothesis
  ("the whole argument is `(r·h)e₁ + i(M)h ≤ e₁f₁h − h < M`, valid at every `h`"). Signed, kept,
  unused.
* *the zero branch is proved from `hσ0` and `map_zero`, not from a valuation computation.* The
  corpus phrases it as "`k̂_t = 0` with valuation `⊤`"; in Lean the polynomial is literally `0`
  (`liftC6_zero`), and `suppVal` of `0` being `⊤` is chapter B's fact, not restated here. Stating
  the branch as `= 0` is strictly more informative than stating the valuation.
* *clause 3's `↔` is over a field and both disjuncts are the corpus's.* `mul_eq_zero` needs no
  domain hypothesis beyond `Field K₁`, and `sub_eq_zero` turns `ϑ − 1 = 0` into `ϑ = 1` with
  `ϑ = η^{W(t)}` supplied by D.18. **The naive recipe is NOT a chapter object** — only the
  criterion is; nothing in this file names or constructs the naive key.

**DEPENDS.** D.16 (`Wfloor`), D.18 (`levelOneArena_vartheta`), D.24 (`liftC6`), D.25
(`liftC6_spec`, `liftC6_zero` — imported as `Uniformity.ChapD.D25a`, which re-exports D.24) ·
mathlib `Module.Basis.repr`, `Finsupp` coercions.

**PROOF.** (1) is D.25 at `l := b.repr (c·η^{W})`: nonzero iff the element is nonzero, because
`Basis.repr` is a linear equiv (`LinearEquiv.map_eq_zero_iff`) and `algebraMap` out of a field is
injective, with `η^{W}` a unit; the zero branch is `map_zero` + `liftC6`'s `hσ0`. (2) is D.18
followed by `mul_inv_cancel₀` at the unit `η^{W}`. (3) is `mul_eq_zero` + `sub_eq_zero` after the
same D.18 rewrite.

SOURCE: `EFF.T1.13` (the boxed `(C3-level-1-key)`, "Its multiplicative coefficient is exactly
`c_t`", the agreement criterion `c_t(ϑ_{i,f_{i+1}−t}−1) = 0`); `EFF.T1.27` (the A3 block: both
branches + `c^mult = Γ_t η^{−W(t)} = c_t`; "T1 **supplies the gauge input to** LEMMA GENTOW-1" —
the OUT-interface, with `EFF.GENTOW1 [supplied-by: chapter C]` on the consumer side);
`EFF.T1.28` (the A4 block: this node + D.25's x-free clause are "the corrected-key and x-free
inputs to THEOREM GENTOW-3").

**TEETH.** T1 §4.2 checks 1 and 2 → **Lean theorem** (this node); the gauge-naive tooth → clause
3 is the exact agreement criterion; §7 attacks 2, 3, 8 → §12.

ENVIRONMENT: ENV-D4 + the `(K₁, η, b)` carrier data.

## Status

Sorry-free, axiom-free (Lean core only): all three are PROVED here, not the leanspec `axiom`
stubs.
-/

namespace Uniformity.Density.Gauge

-- ENV-D4 (blueprint §0.1) = CHAP-B's ENV-A′, MINUS its `{π : O}`: per defect D-D4 this node
-- binds `π` itself, explicitly and first.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- `hh` (D.25's carried ⚠, §14 item 5) and `hb` (the fixed basis `1, η, …, η^{f₁−1}`) are signed
-- hypotheses of the frozen statement and are not consumed: the exact height rides `b.repr`'s
-- injectivity for ANY basis, and D.25 clause 1 needs no `h > 0`. Kept, not removed — the
-- statement is not weakened (the D.25a precedent).
set_option linter.unusedVariables false in
/-- **D.28 clause 1 — `(C3-level-1-key)`, the A3 pin** (`EFF.T1.13`, `EFF.T1.27`): the corrected
level-1 coefficient `k̂_t = L_{M_t}(c_t η^{W(t)})` has exact height `M_t = (f₂−t)u₂` when
`c_t ≠ 0`, and is the zero polynomial (valuation `⊤`) on the zero branch. -/
theorem levelOne_corrected_key (π : O) (e₁ h f₁ f₂ : ℕ) (hπ : Irreducible π) (he : 0 < e₁)
    (hh : 0 < h) (hf : 0 < f₁) (hcop : Nat.Coprime h e₁)
    {K₁ : Type*} [Field K₁] [Algebra (IsLocalRing.ResidueField O) K₁] (η : K₁ˣ)
    (b : Module.Basis (Fin f₁) (IsLocalRing.ResidueField O) K₁)
    (hb : ∀ r, b r = (η : K₁) ^ (r : ℕ))
    (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (u₂ : ℕ) (t : Fin f₂) (hM : e₁ * f₁ * h < (f₂ - (t : ℕ)) * u₂)
    (c : IsLocalRing.ResidueField O) :
    (c ≠ 0 → Uniformity.Density.Leaf.suppVal Polynomial.X
        (liftC6 π e₁ h σ ((f₂ - (t : ℕ)) * u₂)
          (fun r => b.repr (algebraMap (IsLocalRing.ResidueField O) K₁ c
            * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)) r)) h e₁
        = (((f₂ - (t : ℕ)) * u₂ : ℕ) : ℕ∞))
    ∧ (c = 0 → liftC6 π e₁ h σ ((f₂ - (t : ℕ)) * u₂)
        (fun r => b.repr (algebraMap (IsLocalRing.ResidueField O) K₁ c
          * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)) r) = 0) := by
  constructor
  · intro hc
    -- `c ≠ 0` in the residue field ⇒ `c·η^{W(t)} ≠ 0` in `K₁` (`algebraMap` out of a field is
    -- injective; `η^{W}` is a unit).
    have hx : algebraMap (IsLocalRing.ResidueField O) K₁ c
        * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ (Units.ne_zero η))
      exact fun hz => hc ((algebraMap (IsLocalRing.ResidueField O) K₁).injective
        (by rw [hz, map_zero]))
    -- hence the coordinate vector is nonzero, `Basis.repr` being a linear equiv.
    have hl : (fun r => b.repr (algebraMap (IsLocalRing.ResidueField O) K₁ c
        * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)) r)
        ≠ (0 : Fin f₁ → IsLocalRing.ResidueField O) := by
      intro h0
      refine hx ?_
      refine (LinearEquiv.map_eq_zero_iff b.repr).1 ?_
      ext r
      simpa using congrFun h0 r
    exact (liftC6_spec π e₁ h f₁ hπ he hf hcop σ hσ hσ0 _ hM _ hl).2
  · intro hc
    subst hc
    have hzero : (fun r => b.repr (algebraMap (IsLocalRing.ResidueField O) K₁ 0
        * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)) r)
        = (0 : Fin f₁ → IsLocalRing.ResidueField O) := by
      funext r
      simp
    rw [hzero]
    exact liftC6_zero π e₁ h f₁ σ hσ0 _

/-- **D.28 clause 2 — the multiplicative coefficient is exactly `c_t`** (`EFF.T1.13`,
`EFF.T1.27`): `Γ_t·ϑ_{1,f₂−t}⁻¹ = c_t`, with `Γ_t = c_t·η^{W(t)}` and `ϑ_{1,f₂−t} = η^{W(t)}`
by D.18. This is the A3 display `c^mult = Γ_t η^{−W(t)} = c_t`. -/
theorem levelOne_cmult (e₁ h f₂ : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K₁ : Type*} [Field K₁] (η : K₁ˣ) (u₂ : ℕ) (t : Fin f₂) (c : K₁) :
    (c * ((η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)))
        * (((levelOneArena e₁ h he hcop η).vartheta (u₂ : ℤ) (f₂ - (t : ℕ)) : K₁))⁻¹ = c := by
  have hv : (((levelOneArena e₁ h he hcop η).vartheta (u₂ : ℤ) (f₂ - (t : ℕ)) : K₁ˣ) : K₁)
      = (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ) := by
    rw [levelOneArena_vartheta, Wfloor, Units.val_pow_eq_pow_val]
  rw [hv, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero η)), mul_one]

/-- **D.28 clause 3 — the naive/corrected agreement criterion** (`EFF.T1.13`):
`c_t(ϑ_{1,f₂−t} − 1) = 0` iff `c_t = 0` or `η^{W(t)} = 1`. The naive recipe is NOT a chapter
object; only the criterion is, and this is it. -/
theorem levelOne_naive_agree_iff (e₁ h f₂ : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K₁ : Type*} [Field K₁] (η : K₁ˣ) (u₂ : ℕ) (t : Fin f₂) (c : K₁) :
    c * (((levelOneArena e₁ h he hcop η).vartheta (u₂ : ℤ) (f₂ - (t : ℕ)) : K₁) - 1) = 0
      ↔ c = 0 ∨ (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ) = 1 := by
  have hv : (((levelOneArena e₁ h he hcop η).vartheta (u₂ : ℤ) (f₂ - (t : ℕ)) : K₁ˣ) : K₁)
      = (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ) := by
    rw [levelOneArena_vartheta, Wfloor, Units.val_pow_eq_pow_val]
  rw [hv, mul_eq_zero, sub_eq_zero]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.levelOne_corrected_key
#print axioms Uniformity.Density.Gauge.levelOne_cmult
#print axioms Uniformity.Density.Gauge.levelOne_naive_agree_iff

end AxCheck
