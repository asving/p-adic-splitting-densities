/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSviii_a_R5_final
import LeanUrat.Moves.L4_TRANSviii_b_R4
import LeanUrat.MovesGr.HeldUnits_certs

/-!
# HC1.S8_childS6 — D.7(viii): the split axiom transports; child TvecUnitLaw DERIVED

moves_ref: MOVES 2419–2463 (D.7(viii), both halves + consumers). deps: S7; Moves
`L4_TRANSviii_a_R5_final`, `L4_TRANSviii_b_R4` (clean); MovesGr
`tvec_units_fragment` (proved fragment). The child `TvecUnitLaw` is DERIVED from
the parent `StageCoreL.tvec_unit` + `child_Tvec` — the `L4_TRANSvi` held fence
(child T-law not from (ht,M′) alone). The (S6a′)/(S6b′) fields ride the assembled
child Stage; the non-projection content here is the T-law + the previous-read
(I-aug) threshold recursion bottoming at the base. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S8: the child T-vector product law at the actual normalizing unit, and the
child's previous-read (I-aug) law (the two-line mutual recursion's bottoming data),
derived from the parent core + the transition record. -/
theorem S8_childS6 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    TvecUnitLaw σ' ∧ ((σ'.e : ℤ) * σ'.wPrev σ'.Φ < (σ'.h : ℤ)) := by
  refine ⟨?_, ?_⟩
  · -- TvecUnitLaw σ' — OBSTRUCTION (2026-07-27, dual-audited with Codex).
    -- The blueprint claims this is "DERIVED from parent `StageCoreL.tvec_unit` +
    -- `child_Tvec`". That derivation is INCOMPLETE. Reducing `TvecUnitLaw σ'` to a
    -- value equation in `LTwo ↥σ'.K` (units are pinned by value via `IsGrUnit`):
    --   * the outer-`T` and inner-`z` exponents collapse cleanly. Writing
    --     `W := Σᵢ aᵢ·σ.w rᵢ` over the child `Tvec` entries `(rᵢ, aᵢ)`, the parent
    --     product law forces `Σⱼ bⱼ·σ.wPrev uⱼ = σ.s` (parent-B); with `σ.hStretch`
    --     and parent `hbez` this gives `W = σ'.s`, hence outer `T`-power `= 1`
    --     (child `hbez`) and inner `z`-power `= 0`.
    --   * the RESIDUE reduces the whole goal to  `∏ᵢ cᵢ^{aᵢ} = 1`  in `↥σ'.K`,
    --     where `cᵢ` is the child digit scalar of rep `rᵢ` supplied by
    --     `tc.child_dig_frame`: `(cᵢ : F) = σ.digPrime zbar rᵢ · z̄^{mfun (σ.w rᵢ)}`.
    --   * taking `F`-images and using parent-B + the parent scalar law
    --     `∏ⱼ dⱼ^{bⱼ} = 1` (parent-⋆⋆), the `digPrime` factors cancel to `1`, leaving
    --         ∏ᵢ (cᵢ : F)^{aᵢ}  =  z̄^{σ'.s · E},   E := Σⱼ bⱼ·mfun(σ.w uⱼ) + σ.t·mfun(σ.h).
    -- So (given every hypothesis in scope)  `TvecUnitLaw σ'  ⟺  z̄^{σ'.s·E} = 1`.
    -- NOTHING in scope forces this: `mfun : ℤ → ℤ` is only existentially supplied by
    -- `child_dig_frame` (coherent = a function of the parent weight, but its VALUES are
    -- unpinned); `σ'` carries only bare `Stage` laws (no `StageCoreL`/`CoeffLocLaw σ'`
    -- — those are S9's job). The one bare-`Stage` handle, `σ'.hRmul`, gives at most
    -- additivity of `mfun` mod ord(z̄) on the tiny sub-monoid of weights whose
    -- realizers' PRODUCTS stay in `C_Φ̂` (`inC` = `deg <`, so products generically
    -- leave it); and even FULL additivity yields `E = mfun 1` (via
    -- `Σⱼ bⱼ·σ.w uⱼ + σ.t·σ.h = 1`), so the frame twist `z̄^{σ'.s·mfun 1}` is still
    -- uncontrolled. This is the same interface-underspecification class as the
    -- documented `MovesGr.L4_genuine_imp_stageCoreL`: the product-law leg of
    -- `TvecUnitLaw` is not derivable from the recorded transition data. Honest fix is
    -- UPSTREAM (pin `child_dig_frame`'s `mfun` — e.g. the D.7(vi) `z̄`-normalization
    -- that makes the child T-vector product law hold — or hypothesize `StageCoreL σ'`).
    --
    -- ESCALATION CERTIFICATE (2026-07-28, Fable + Codex fresh-context audit: findings
    -- 1–11, 13 all CONFIRMED, sole gap = instance inhabitation, inherent): the
    -- obstruction is upgraded from "the known reductions fail" to a TWIST SYMMETRY of
    -- the ENTIRE hypothesis class, ruling out every possible route. With
    -- ẑ := z̄ ∈ ↥σ'.K (via `child_field`), r := ord z̄, and λ : ℤ, define σ̃' := σ'
    -- with only `R` replaced by `R̃ f := C (ẑ^{λ·σ'.w f}) * σ'.R f`. Then:
    --   * every Stage law of σ' survives (hRmul via hwmul; hRadd/hRlt since equal-w
    --     terms twist equally and `w f < w g → σ'.w (f+g) = σ'.w f` is derivable;
    --     hS5/hS6b for ALL λ; hRΦ iff r ∣ λ·h'; hS6a if z̄^{λe'} ∈ FQ);
    --   * `child_dig_frame` survives with `mfun + λe'·id`; every OTHER hypothesis
    --     (TransitionData, child_Tvec, TransHyp, parent StageCoreL) never mentions
    --     σ'.R, so survives verbatim;
    --   * the pinned TvecUnitLaw product gains EXACTLY `C (C (ẑ^{λ·D}))` with
    --     D = σ'.s·e'·W + σ'.t·h' and W = 1 forced by the parent product law (outer
    --     T-degrees; σ.Φ and the parent reps are child coefficients via σ'.hreps ∘
    --     child_reps), so D = 1 by the child Bézout: the product shifts by ẑ^λ.
    -- At λ-admitting numerics — e.g. K = FQ = 𝔽₃ ≤ F ⊇ 𝔽₉, z̄ a generator of 𝔽₉ˣ
    -- (r = 8, g = 2), (e', h') = (1, 8) (t' = 0, s' = 1), λ = 4: 8 ∣ 32, z̄⁴ = −1 ∈ 𝔽₃,
    -- 8 ∤ 4 — the twist preserves ALL hypotheses and multiplies the pinned product by
    -- C (C (−1)) ≠ 1, so `TvecUnitLaw` cannot hold for both σ' and σ̃'. Hence NO proof
    -- of this conjunct exists unless the hypothesis class is uninhabited at every such
    -- numeric (it is not, for any faithful interface: genuine towers with these reads
    -- exist). The interface pins only z̄^{λh'} = 1 and z̄^{λe'} ∈ FQ — never z̄^λ = 1.
    -- CONSUMER NOTE: S9 CONSTRUCTS σ' (chooses σ'.R = the D.7(vi)-normalized residual
    -- of the transported unit), where the product law holds BY CONSTRUCTION — the
    -- corpus needs S8's conclusion only for S9's σ', not for an arbitrary recorded σ'.
    sorry
  · -- (I-aug) at the child's previous read: e'·wPrev Φ̂ = e'·w Φ̂ < h'
    have he : σ'.e = e' := tc.base.child_e
    have hh : σ'.h = h' := tc.base.child_h
    have hk : σ'.Φ = Φhat := tc.base.child_key
    have hthr : σ'.wPrev Φhat = σ.w Φhat := tc.base.threshold
    rw [he, hh, hk, hthr]
    exact th.hiaug

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S8_childS6
