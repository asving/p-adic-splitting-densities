/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D49

/-!
# Uniformity.ChapD.D50 — LEMMA T4.2(b): perturbation stability

**Chapter D, NODE D.50** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the
certificate witness (T4); amendments A-1, A-D.1 govern — this node's signature is unamended).
ENVIRONMENT: as D.46 (ENV-D3 plus the two extra parameters `(Dv, Slot)`; binders inline, no
`variable` block — B.42). Two public declarations: the signed theorem and the signed sibling
corollary named in the blueprint's SIGNATURE block.

*Perturbation stability.* For a perturbation `g : Dv` whose sum with the key power stays in the
member class — `f := f_key + g ∈ 𝔐`, "a pure coefficient condition" (`EFF.T4.05`) —

```
grΔ (Θ_j) j g = 0                    →  grΔ (Θ_j) j (f_key + g) = ω_j     (perturb_stable)
(∀ m ≤ Θ_j, grΔ m j g = 0) ∧ Touched j →  ν_j (f_key + g) = Θ_j           (perturb_nu_eq)
```

the second display for `j < μ₂`. The first is the frame-level content of `EFF.T4.15`: the
certificate witness of the key power survives any perturbation that is silent at height `Θ_j`.
The second is the corpus's **in-budget SPECIALIZATION** — "every touched coordinate remains
divergent exactly at `Θ_j` under such an in-budget perturbation".

## The route (`EFF.T4.15`'s proof)

1. **The theorem is linearity and nothing else.** "`Δ_j(f) = Δ_j(f_key) + Δ_j(g)`; taking the
   height-`Θ_j` graded component proves the first assertion." In the frame that is `map_add` on
   D.46's `grΔ` — an `AddMonoidHom` precisely because "linearity is the ONLY property used
   downstream" (`EFF.T4.06`) — followed by `hg` and `add_zero`; the residue
   `grΔ (Θ_j) j f_key = ω_j` is D.48's definition, so the last step is `rfl`.
2. **The corollary is D.49's `sInf` arithmetic re-run at `f_key + g`.** (FLOOR) applied at `hf`
   (not at `fkey_mem`) kills every height `m < Θ_j`, so `Θ_j ≤ ν_j(f_key + g)`; the margin
   hypothesis at `m = Θ_j` feeds step 1, and `Touched j` then makes the height-`Θ_j` digit of
   `f_key + g` literally `ω_j ≠ 0`, so `Θ_j` is a member of D.47's set and `sInf_le` gives the
   reverse inequality.

## IMPORT FENCE (PE1(3)'s exact check)

**The withdrawn "same shift" inference is NOT used.** Nothing in either proof relates the shift
of `g` to the shift of `f_key`, or transports an attainment statement from one to the other; the
only facts consumed about `g` are the displayed vanishing hypotheses. The deep-perturbation
parenthetical of `EFF.T4.15` is likewise decoupled: `perturb_stable` says nothing about heights
other than `Θ_j`, and a perturbation with content BELOW `Θ_j` is excluded here only through the
frame's own (FLOOR) at `hf`, never through a claim about `g`'s shift.

**The margin enters ONLY as the displayed hypothesis.** `hg : ∀ m ≤ Θ_j, grΔ m j g = 0` is the
Lean spelling of the supplier's "S8.1 repaired margin ledger places every discrepancy of `g` at
height at least `Θ_j + 1`". Its discharge is the supplier's S8.1 box — membership fact 2 plus the
ledger, `EFF.GENTOW3 [supplied-by: chapter C]` at D.53 — and NOT anything proved in chapter D.
`EFF.T4.15`'s own conditionality is verbatim: "the in-budget case is a *specialization*, supplied
by S8.1's box". Consequently `perturb_nu_eq` is a conditional theorem whose antecedent is an
external obligation; it asserts nothing about perturbations outside the budget.

## Faithfulness

**`hf` is carried, not consumed, in `perturb_stable`.** The frozen signature displays
`hf : F.fkey + g ∈ F.M` and the proof does not use it (step 1 is pure linearity). The hypothesis
is KEPT — the statement is not weakened, and the corpus states T4.2(b) for members `f ∈ 𝔐` — so
the unused-variable linter is switched off at that declaration only, on the D.23/D.25a/D.34b
precedent. In `perturb_nu_eq` the same hypothesis IS consumed: it is the only route to (FLOOR)
at `f_key + g`, which is the lower bound.

**`hg` is stated at `≤ Θ_j`, not at `< Θ_j`.** The corollary needs the height-`Θ_j` digit of `g`
to vanish (that is what step 1 consumes at `m = Θ_j`); the heights strictly below are already
handled by (FLOOR) at `hf`, so the `< Θ_j` part of `hg` is redundant with the frame but is kept
because the frozen signature and the supplier's ledger both quantify over `m ≤ Θ_j`.

**`hj : j < F.μ₂` is necessary in the corollary and absent from the theorem.** The theorem is a
pure `map_add` identity, true at every `j`. The corollary's lower bound is (FLOOR), which D.46
supplies only on the coordinate range; without `hj` it is false — a frame with a nonzero
`grΔ m j (f_key + g)` at some `m < Θ_j` outside the range would give `ν_j(f_key + g) < Θ_j`.

**`Touched j` is about `f_key`, not about `f_key + g`.** D.48's `Touched j := ω_j ≠ 0` and
`ω_j := grΔ (Θ_j) j f_key`, so the corollary's hypothesis is a statement about the key power; the
conclusion transfers attainment to the perturbed member through step 1's identity. No
member-general converse is inferred (D.49's fence, D.52's ⚠ (ii)).

**No new definition** — nothing is added to the trust boundary beyond D.46/D.47/D.48's own
flagged definitions.

DEPENDS: D.46 (`CertFrame`, its `floor` field), D.47 (`CertFrame.nuIdx`), D.48
(`CertFrame.omega`, `CertFrame.Touched`), D.49 (imported; its two signed declarations are the
siblings of this node's corollary, whose `sInf` arithmetic is re-run here at `f_key + g` because
D.49's helpers are `private` and keyed to `f_key`) — all landed at `Uniformity.ChapD.D46`–`D49` ·
mathlib `map_add`, `add_zero`, `le_antisymm`, `sInf_le`, `le_sInf`, and the `ℕ → ℕ∞` cast lemmas
reached by `exact_mod_cast`.

SOURCE: `EFF.T4.15` (statement and proof, R2-G2 as rebound by R5-F1(2)/(3); the deep-perturbation
parenthetical decoupling note; the conditionality of the in-budget specialization).

**TEETH.** S8 PE1(3) → **this Lean theorem** (the import fence above is the scored half: the
withdrawn "same shift" inference is absent). PE2 GT3 consumption → D.53/§12; the `CertFrame`
inhabitation witness that makes these statements non-vacuous is D.68's census row (A-D.1
addition (v)), not duplicated here.

ENVIRONMENT: as D.46 — ENV-D3 (`[Field K]` for the digit field) plus `(Dv, Slot)`, written inline
as each declaration's own binders.

## Status

Sorry-free, axiom-free (Lean core only): both declarations are PROVED theorems here, not the
leanspec `axiom` stubs.
-/

namespace Uniformity.Density.Gauge

-- `hf` is signed but inert here: step 1 is pure linearity, so the membership fact is displayed
-- per the frozen statement and not consumed (D.23/D.25a/D.34b precedent).
set_option linter.unusedVariables false in
/-- **D.50 — LEMMA T4.2(b): perturbation stability** (`EFF.T4.15`).  For a perturbation `g` with
`f_key + g ∈ 𝔐` (a pure coefficient condition) that is silent at height `Θ_j`, the assembled
height-`Θ_j` digit of the perturbed member is the certificate witness itself:
`grΔ (Θ_j) j (f_key + g) = ω_j`.  The proof is `EFF.T4.15`'s "`Δ_j(f) = Δ_j(f_key) + Δ_j(g)`;
taking the height-`Θ_j` graded component" — `map_add` on D.46's additive `grΔ`.
⚠ IMPORT FENCE: the withdrawn "same shift" inference is NOT used; `g` enters only through `hg`.
`hf` is displayed per the frozen statement and is not consumed (the unused-variable linter is
silenced for that reason at this declaration alone). -/
theorem CertFrame.perturb_stable {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {g : Dv} (hf : F.fkey + g ∈ F.M)
    (hg : F.grΔ (F.Θ j) j g = 0) :
    F.grΔ (F.Θ j) j (F.fkey + g) = F.omega j := by
  rw [map_add, hg, add_zero]
  rfl

/-- **D.50 — the in-budget SPECIALIZATION** (`EFF.T4.15`).  If the perturbation is silent at
every height `m ≤ Θ_j` — the supplier's "S8.1 repaired margin ledger places every discrepancy of
`g` at height at least `Θ_j + 1`" — and the coordinate is touched, then "every touched coordinate
remains divergent exactly at `Θ_j` under such an in-budget perturbation":
`ν_j (f_key + g) = Θ_j`.
⚠ CONDITIONAL: the margin enters ONLY as the displayed hypothesis `hg`, whose discharge is the
supplier's S8.1 box (membership fact 2 + the ledger, `EFF.GENTOW3 [supplied-by: chapter C]`,
D.53).  Nothing here asserts anything about perturbations outside that budget. -/
theorem CertFrame.perturb_nu_eq {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {g : Dv} (hj : j < F.μ₂) (hf : F.fkey + g ∈ F.M)
    (hg : ∀ m, m ≤ F.Θ j → F.grΔ m j g = 0) (ht : F.Touched j) :
    F.nuIdx j (F.fkey + g) = (F.Θ j : ℕ∞) := by
  -- Step 1 at `m = Θ_j`: the perturbed height-`Θ_j` digit IS the certificate witness.
  have hdig : F.grΔ (F.Θ j) j (F.fkey + g) = F.omega j :=
    F.perturb_stable hf (hg (F.Θ j) le_rfl)
  refine le_antisymm (sInf_le ⟨F.Θ j, rfl, ?_⟩) ?_
  · -- `Θ_j` is a member of D.47's set for `f_key + g`, because `ω_j ≠ 0`.
    rw [hdig]
    exact ht
  · -- (FLOOR) at `hf` — the perturbed member is in `𝔐` — kills every height below `Θ_j`.
    refine le_sInf ?_
    intro m hm
    obtain ⟨m', rfl, hm'⟩ := hm
    have hle : F.Θ j ≤ m' := by
      by_contra hlt
      exact hm' (F.floor (F.fkey + g) hf j hj m' (by omega))
    exact_mod_cast hle

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame.perturb_stable
#print axioms Uniformity.Density.Gauge.CertFrame.perturb_nu_eq

end AxCheck
