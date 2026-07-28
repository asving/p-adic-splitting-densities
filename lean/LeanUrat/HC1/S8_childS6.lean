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
# HC1.S8_childS6 — D.7(viii): the child's previous-read (I-aug) law (F-4 restated)

moves_ref: MOVES 2419–2463 (D.7(viii), both halves + consumers). deps: S7; Moves
`L4_TRANSviii_a_R5_final`, `L4_TRANSviii_b_R4` (clean); MovesGr
`tvec_units_fragment` (proved fragment). The (S6a′)/(S6b′) fields ride the
assembled child Stage.

**F-4 RESTATEMENT (sign-off event 2026-07-28, blueprint §9.4):** the E-phase form
also concluded `TvecUnitLaw σ'`, claimed "DERIVED from parent
`StageCoreL.tvec_unit` + `child_Tvec`". That conjunct was REFUTED over the
recorded hypothesis class by a TWIST SYMMETRY (dual-audited Fable + Codex,
findings 1–11, 13 CONFIRMED) — the certificate is retained verbatim below. The
note PINS the twist (D.7(vi), MOVES 2395–2402: `V′ := Π_i in_{w′}(ũ_i)^{s·b_i} ·
in_{w′}(Φ)^{t}`, `u₀ := V′^{−h′}` "explicit, no choice", `z′ := u₀·Y′^{e′}`;
2410–2414: the next stage's pinned unit is V′ and the D.3(b) literal identity
re-runs verbatim) — the z̄-twist freedom exists only in the Lean record
(`child_dig_frame`'s `∃ mfun`), an interface under-recording, NOT a note gap. Per
the stuck rule the statement gains the pin, and the honest carrier of the pin is
the CONSTRUCTION: **the TvecUnitLaw conjunct MOVES to S9d** (blueprint §9.5),
stated of S9's constructed child, where `K1_vertexPin.K1_tvecUnitLaw_of_pin`
closes it from the recorded `VertexPin`. S8 keeps its PROVED leg: the child
previous-read (I-aug) law — a theorem, no sorry. difficulty: easy (post-F-4).
hyp: none.

ESCALATION CERTIFICATE (retained; the certificate that no recorded-σ′ form of the
former TvecUnitLaw conjunct is provable — 2026-07-28, Fable + Codex fresh-context
audit; sole gap = instance inhabitation, inherent): with ẑ := z̄ ∈ ↥σ'.K (via
`child_field`), r := ord z̄, and λ : ℤ, the twist σ̃′ := σ′ with only `R` replaced
by `R̃ f := C (ẑ^{λ·σ'.w f}) * σ'.R f` preserves EVERY Stage law of σ′ (hRmul via
hwmul; hRadd/hRlt since equal-w terms twist equally; hS5/hS6b for ALL λ; hRΦ iff
r ∣ λ·h′; hS6a if z̄^{λe′} ∈ FQ), preserves `child_dig_frame` (via mfun + λe′·id)
and every other hypothesis in scope (none mention σ′.R), yet multiplies the pinned
TvecUnitLaw product by EXACTLY `C (C (ẑ^{λ·D}))` with D = σ'.s·e'·W + σ'.t·h' and
W = 1 forced by the parent product law, so D = 1 by the child Bézout: the product
shifts by ẑ^λ. At λ-admitting numerics — K = FQ = 𝔽₃ ≤ F ⊇ 𝔽₉, z̄ a generator of
𝔽₉ˣ (r = 8, g = 2), (e', h') = (1, 8) (t' = 0, s' = 1), λ = 4: 8 ∣ 32, z̄⁴ = −1 ∈
𝔽₃, 8 ∤ 4 — the twist preserves ALL hypotheses and multiplies the pinned product
by C (C (−1)) ≠ 1, so TvecUnitLaw cannot hold for both σ′ and σ̃′. The interface
pins only z̄^{λh′} = 1 and z̄^{λe′} ∈ FQ — never z̄^λ = 1. CONSUMER NOTE: S9
CONSTRUCTS σ′ (the D.7(vi)-normalized residual), where the product law holds BY
CONSTRUCTION — the corpus needs the T-law only for S9's σ′, not for an arbitrary
recorded σ′.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S8 (F-4 restated shape): the child's previous-read (I-aug) law — the
two-line mutual recursion's bottoming data — derived from the move's own `hiaug` +
the transition record. (The former `TvecUnitLaw σ'` conjunct is S9d's, by
construction — see the header certificate.) -/
theorem S8_childS6 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    (σ'.e : ℤ) * σ'.wPrev σ'.Φ < (σ'.h : ℤ) := by
  -- (I-aug) at the child's previous read: e'·wPrev Φ̂ = e'·w Φ̂ < h'
  have he : σ'.e = e' := tc.base.child_e
  have hh : σ'.h = h' := tc.base.child_h
  have hk : σ'.Φ = Φhat := tc.base.child_key
  have hthr : σ'.wPrev Φhat = σ.w Φhat := tc.base.threshold
  rw [he, hh, hk, hthr]
  exact th.hiaug

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S8_childS6
